-- Prove2me | solution 1 for OAI.CurrentKS.RationalSDP.valueQueryPoint_correct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:32.467544+00:00
-- url     : https://prove2.me/submissions/3ce60e47-c09f-419f-8f4d-3ca0fc8e8e21

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_RationalSDP_valuePencil_ball
import Theorems.Thm_OAI_CurrentKS_State_etaTheta_minimizer

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ConvexInnerBall
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalOptimization
noncomputable section
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma convex_innerBall (K : Set E) (hK : Convex ℝ K) (z c : E) (hz : z ∈ K)
    {r a : ℝ} (hball : Metric.closedBall c r ⊆ K) (ha : 0 < a) (ha1 : a ≤ 1) :
    Metric.closedBall ((1-a) • z+a • c) (a*r) ⊆ K := by
  intro y hy
  let e := y-((1-a) • z+a • c)
  have he : ‖e‖ ≤ a*r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hu : c+a⁻¹ • e ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    have hh : c+a⁻¹ • e-c = a⁻¹ • e := by abel
    rw [hh,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹*(a*r) := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ha.le)
      _ = r := by field_simp
  have hc := hK hz (hball hu) (sub_nonneg.mpr ha1) ha.le (by ring : 1-a+a = 1)
  have hcomb : (1-a) • z+a • (c+a⁻¹ • e) = y := by
    dsimp [e]
    rw [smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
    abel
  rwa [hcomb] at hc

lemma innerBall_objective (f : E →L[ℝ] ℝ) (z c : E) {L R r a : ℝ}
    (hL : ‖f‖ ≤ L) (hz : ‖z‖ ≤ R) (hc : ‖c‖ ≤ R)
    (ha : 0 ≤ a) (y : E)
    (hy : y ∈ Metric.closedBall ((1-a) • z+a • c) (a*r)) :
    f y ≤ f z + a*L*(2*R+r) := by
  have hLp : 0 ≤ L := le_trans (norm_nonneg f) hL
  have he : ‖y-((1-a) • z+a • c)‖ ≤ a*r := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
  have hdist : ‖y-z‖ ≤ a*(2*R+r) := by
    have hx : y-z = (y-((1-a) • z+a • c))+a • (c-z) := by module
    rw [hx]
    calc
      _ ≤ ‖y-((1-a) • z+a • c)‖+‖a • (c-z)‖ := norm_add_le _ _
      _ ≤ a*r+a*(2*R) := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha]
        have hh := norm_sub_le c z
        gcongr
        linarith
      _ = _ := by ring
  calc
    f y = f z+f (y-z) := by rw [map_sub]; ring
    _ ≤ f z+‖f (y-z)‖ := add_le_add_right (le_abs_self _) _
    _ ≤ f z+‖f‖*‖y-z‖ := add_le_add_right (f.le_opNorm _) _
    _ ≤ f z+L*(a*(2*R+r)) := by
      exact add_le_add_right (mul_le_mul hL hdist (norm_nonneg _) hLp) _
    _ = _ := by ring

theorem nearOptimal_innerBall (K : Set E) (hK : Convex ℝ K) (f : E →L[ℝ] ℝ)
    (z c : E) (hzK : z ∈ K) {L R r δ : ℝ}
    (hL : ‖f‖ ≤ L) (hLp : 0 < L) (hR : 0 ≤ R) (hr : 0 < r)
    (hz : ‖z‖ ≤ R) (hc : ‖c‖ ≤ R) (hball : Metric.closedBall c r ⊆ K)
    (hδ : 0 < δ) (hδsmall : δ ≤ L*(2*R+r)) :
    let a := δ/(L*(2*R+r))
    Metric.closedBall ((1-a) • z+a • c) (a*r) ⊆ K ∩ {y | f y ≤ f z+δ} := by
  dsimp only
  let a := δ/(L*(2*R+r))
  have hden : 0 < L*(2*R+r) := mul_pos hLp (by linarith)
  have ha : 0 < a := div_pos hδ hden
  have ha1 : a ≤ 1 := (div_le_one hden).mpr hδsmall
  intro y hy
  refine ⟨convex_innerBall K hK z c hzK hball ha ha1 hy,?_⟩
  have ho := innerBall_objective f z c hL hz hc ha.le y hy
  have he : a*L*(2*R+r) = δ := by dsimp [a]; field_simp
  simp only [he] at ho
  exact ho

end
end CurrentKS.RationalOptimization

open Matrix

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ExactStepDecrease
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalOptimization
noncomputable section
open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma exact_step_decrease (y c v : E) {r : ℝ} (hr : 0 ≤ r)
    (hv : ‖v‖ ≤ 1) (hsep : r ≤ inner ℝ v (c-y)) :
    ‖y+r • v-c‖^2 ≤ ‖y-c‖^2-r^2 := by
  have he : y+r • v-c = (y-c)+r • v := by abel
  rw [he,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
  have hi : inner ℝ (y-c) v ≤ -r := by
    rw [real_inner_comm] at hsep
    have hh : inner ℝ (y-c) v = -(inner ℝ (c-y) v) := by
      rw [← inner_neg_left]
      congr 1
      abel
    linarith
  have hv0 := norm_nonneg v
  have hv2 : ‖v‖^2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hi hr
  have ht := mul_le_mul_of_nonneg_left hv2 (sq_nonneg r)
  nlinarith

lemma rounded_step_decrease (y c v y' : E) {r R δ : ℝ}
    (hr : 0 ≤ r) (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hy : ‖y-c‖ ≤ R)
    (hv : ‖v‖ ≤ 1) (hsep : r ≤ inner ℝ v (c-y))
    (hround : ‖y'-(y+r • v)‖ ≤ δ)
    (hsmall : 2*(R+r)*δ+δ^2 ≤ r^2/2) :
    ‖y'-c‖^2 ≤ ‖y-c‖^2-r^2/2 := by
  have hstep := exact_step_decrease y c v hr hv hsep
  have hnorm : ‖y+r • v-c‖ ≤ R+r := by
    have he : y+r • v-c = (y-c)+r • v := by abel
    rw [he]
    calc
      _ ≤ ‖y-c‖+‖r • v‖ := norm_add_le _ _
      _ ≤ R+r := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]; nlinarith
  have hn : ‖y'-c‖ ≤ ‖y+r • v-c‖+δ := by
    calc
      _ = ‖(y+r • v-c)+(y'-(y+r • v))‖ := by congr 1; abel
      _ ≤ ‖y+r • v-c‖+‖y'-(y+r • v)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hround _
  have hn0 := norm_nonneg (y+r • v-c)
  have hn' := sq_le_sq₀ (norm_nonneg (y'-c)) (add_nonneg hn0 hδ) |>.mpr hn
  have hh := mul_le_mul hnorm (le_refl δ) hδ (add_nonneg hR hr)
  nlinarith

lemma separating_margin (K : Set E) (c y v : E) {r b : ℝ}
    (hr : 0 ≤ r) (hball : Metric.closedBall c r ⊆ K)
    (hv : ‖v‖ = 1) (hsep : ∀ z ∈ K, b ≤ inner ℝ v z)
    (hy : inner ℝ v y ≤ b) : r ≤ inner ℝ v (c-y) := by
  have hz : c-r • v ∈ Metric.closedBall c r := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    have he : c-r • v-c = -(r • v) := by abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,hv,mul_one]
  have hs := hsep _ (hball hz)
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hv] at hs
  rw [inner_sub_right]
  nlinarith

end
end CurrentKS.RationalOptimization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_Realification
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W08.realifyVector_complexify _root_.OAI.KS.W08.realifyVector_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped BigOperators

theorem realify_injective {m n : Type*} :
    Function.Injective (@realify m n) := by
  intro A B h
  apply Matrix.ext
  intro i j
  apply Complex.ext
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · exact congrFun (congrFun h (Sum.inr i)) (Sum.inl j)

theorem realify_mul {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    realify (A * B) = realify A * realify B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Complex.mul_re,
      Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib] <;> ring

theorem realify_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n ℂ) (v : n → ℂ) :
    realifyVector (A *ᵥ v) = realify A *ᵥ realifyVector v := by
  funext i
  rcases i with i | i <;>
    simp [realifyVector, realify, Matrix.fromBlocks, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] <;> ring

end KS.W08

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_RealifyAdd
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace KS.W08
open Matrix
open scoped BigOperators

variable {m n p : Type*}

lemma realify_add (A B : Matrix m n ℂ) : realify (A+B)=realify A+realify B := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks, neg_add_rev, add_comm]
lemma realify_zero : realify (0 : Matrix m n ℂ)=0 := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks]
lemma realify_smul (r : ℝ) (A : Matrix m n ℂ) : realify (r • A)=r • realify A := by
  ext i j
  cases i <;> cases j <;> simp [realify, Matrix.fromBlocks]
lemma realify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix m n ℂ) :
    realify (∑ i ∈ s,A i)=∑ i ∈ s,realify (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [realify_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,realify_add,ih]
end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_RealificationSPD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W08

open Matrix
open scoped ComplexOrder BigOperators

theorem realify_conjTranspose {m n : Type*} (A : Matrix m n ℂ) :
    realify Aᴴ = (realify A)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [realify, Matrix.fromBlocks, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem realify_isHermitian {n : Type*} (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (realify A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := congrFun (congrFun (realify_conjTranspose A) j) i
  rw [hA] at h
  simpa using h

theorem realifyVector_dotProduct {n : Type*} [Fintype n] (x y : n → ℂ) :
    realifyVector x ⬝ᵥ realifyVector y = (star x ⬝ᵥ y).re := by
  simp [realifyVector, dotProduct, Fintype.sum_sum_type, Complex.mul_re,
    Finset.sum_add_distrib]

end KS.W08

end

end OAI
end

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeWitness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem quadratic_single {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single i 1) = M i i := by
  simp [single_dotProduct]

theorem negativeDiagonal_witness {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i : Fin n) (hi : M i i < 0) :
    Pi.single i 1 ⬝ᵥ (M *ᵥ Pi.single i 1) < 0 := by
  simpa only [quadratic_single] using hi

theorem quadratic_twoSingle {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (a b : ℚ) :
    (Pi.single i a + Pi.single j b) ⬝ᵥ (M *ᵥ (Pi.single i a + Pi.single j b)) =
      a * (M i i * a + M i j * b) + b * (M j i * a + M j j * b) := by
  simp only [add_dotProduct, single_dotProduct, Matrix.mulVec,
    dotProduct_add, dotProduct_single]

theorem zeroPivotWitness_value {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (hii : M i i = 0) (hij : M i j ≠ 0)
    (hsymm : M j i = M i j) :
    zeroPivotWitness M i j ⬝ᵥ (M *ᵥ zeroPivotWitness M i j) = -1 := by
  unfold zeroPivotWitness
  rw [quadratic_twoSingle, hii, hsymm]
  field_simp [hij]
  ring

theorem zeroPivotWitness_negative {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (i j : Fin n) (hii : M i i = 0) (hij : M i j ≠ 0)
    (hsymm : M j i = M i j) :
    zeroPivotWitness M i j ⬝ᵥ (M *ᵥ zeroPivotWitness M i j) < 0 := by
  rw [zeroPivotWitness_value M i j hii hij hsymm]
  decide

end KS.W17

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

theorem trailingMatrix_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (trailingMatrix M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact hM.apply i.succ j.succ

theorem schurTail_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (schurTail M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [schurTail]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ, hM.apply 0 i.succ]
  rw [mul_comm (M 0 j.succ) (M 0 i.succ)]

theorem firstNonzeroOffDiagonal_some {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (j : Fin n)
    (h : firstNonzeroOffDiagonal M = some j) : M 0 j.succ ≠ 0 := by
  have hj := List.find?_some h
  simpa using hj

theorem firstNonzeroOffDiagonal_none_iff {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    firstNonzeroOffDiagonal M = none ↔ ∀ j : Fin n, M 0 j.succ = 0 := by
  simp [firstNonzeroOffDiagonal, List.find?_eq_none]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PSDSeparation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem psdCutEvalReal_cast {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) :
    psdCutEvalReal q (fun i j => (M i j : ℝ)) = (psdCutEval q M : ℝ) := by
  simp [psdCutEvalReal, psdCutEval, dotProduct, Matrix.mulVec,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_neg]

theorem psdCutEvalReal_nonpos {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    psdCutEvalReal q M ≤ 0 := by
  have h := hM.dotProduct_mulVec_nonneg (fun i => (q i : ℝ))
  simpa [psdCutEvalReal] using neg_nonpos.mpr h

theorem psdWitness_separates {n : ℕ} (q : Fin n → ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hneg : q ⬝ᵥ (M *ᵥ q) < 0) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 := by
  constructor
  · rw [psdCutEvalReal_cast]
    have hr : 0 < psdCutEval q M := neg_pos.mpr hneg
    exact_mod_cast hr
  · exact fun B hB => psdCutEvalReal_nonpos q B hB

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationSoundness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem quadratic_zero_cons {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    Fin.cons 0 y ⬝ᵥ (M *ᵥ Fin.cons 0 y) = y ⬝ᵥ (trailingMatrix M *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, trailingMatrix]

theorem rationalNegativeWitness_sound (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) (q : Fin n → ℚ)
    (hout : rationalNegativeWitness n M = some q) : q ⬝ᵥ (M *ᵥ q) < 0 := by
  induction n with
  | zero => simp [rationalNegativeWitness] at hout
  | succ n ih =>
      by_cases hnegative : M 0 0 < 0
      · have hq : Pi.single 0 1 = q := by
          simpa [rationalNegativeWitness, hnegative] using hout
        subst q
        exact negativeDiagonal_witness M 0 hnegative
      · by_cases hzero : M 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal M with
          | some j =>
              have hq : zeroPivotWitness M 0 j.succ = q := by
                simpa [rationalNegativeWitness, hnegative, hzero, hfind] using hout
              subst q
              exact zeroPivotWitness_negative M 0 j.succ hzero
                (firstNonzeroOffDiagonal_some M j hfind) (hM.apply 0 j.succ)
          | none =>
              cases hrec : rationalNegativeWitness n (trailingMatrix M) with
              | none =>
                  simp [rationalNegativeWitness, hzero, hfind, hrec] at hout
              | some y =>
                  have hq : Fin.cons 0 y = q := by
                    simpa [rationalNegativeWitness, hnegative, hzero, hfind, hrec] using hout
                  subst q
                  rw [quadratic_zero_cons]
                  exact ih (trailingMatrix M) (trailingMatrix_isSymm M hM) y hrec
        · cases hrec : rationalNegativeWitness n (schurTail M) with
          | none =>
              simp [rationalNegativeWitness, hnegative, hzero, hrec] at hout
          | some y =>
              have hq : schurWitnessLift M y = q := by
                simpa [rationalNegativeWitness, hnegative, hzero, hrec] using hout
              subst q
              rw [KS.W07.fin_schurWitnessLift_quadratic M hM hzero y]
              exact ih (schurTail M) (schurTail_isSymm M hM) y hrec

theorem computedPSDSeparator_separates (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) (q : Fin n → ℚ)
    (hout : rationalNegativeWitness n M = some q) :
    0 < psdCutEvalReal q (fun i j => (M i j : ℝ)) ∧
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.PosSemidef → psdCutEvalReal q B ≤ 0 :=
  psdWitness_separates q M (rationalNegativeWitness_sound n M hM q hout)

end KS.W17

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

theorem pivotBlock_posSemidef_iff {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    (pivotBlock a b D).PosSemidef ↔ (pivotSchur a b D).PosSemidef := by
  constructor
  · exact pivotSchur_posSemidef ha b D
  · intro hS
    let _ := scalarPivotInvertible (ne_of_gt ha)
    have hS' : (D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
        (pivotRow b)).PosSemidef := by
      rwa [real_pivot_schur_formula (ne_of_gt ha)]
    have h := (Matrix.PosDef.fromBlocks₁₁
      (pivotRow b) D (scalarPivot_posDef ha)).mpr hS'
    exact h

theorem zero_pivotBlock_posSemidef (D : Matrix n n ℝ) (hD : D.PosSemidef) :
    (pivotBlock 0 (fun _ => 0) D).PosSemidef := by
  change (Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 D).PosSemidef
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) hD.isHermitian
  · intro x
    have hx : Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) = x := Sum.elim_comp_inl_inr x
    have h := hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
    rw [← hx]
    simpa [Matrix.fromBlocks_mulVec, Function.comp_def] using h

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

theorem fin_psd_of_schurTail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : 0 < M 0 0)
    (hS : ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  apply (pivotBlock_posSemidef_iff (by exact_mod_cast ha) _ _).mpr
  rw [← rat_pivotSchur_cast, fin_pivotSchur M hM]
  exact hS

theorem fin_psd_of_zero_pivot_tail {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 = 0) (hrow : ∀ j : Fin n, M 0 j.succ = 0)
    (hD : ((KS.W17.trailingMatrix M).map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv (pivotIndexEquiv n)).mp
  change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
    (fun q : ℚ => (q : ℝ))).PosSemidef
  rw [fin_pivotBlock M hM, rat_pivotBlock_cast]
  simp only [ha, hrow, Rat.cast_zero]
  exact zero_pivotBlock_posSemidef _ hD

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_EliminationCompleteness
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

open Matrix

theorem rationalNegativeWitness_none_psd (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm)
    (hout : rationalNegativeWitness n M = none) :
    (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  induction n with
  | zero =>
      have hz : M.map (fun q : ℚ => (q : ℝ)) = 0 := by
        ext i j
        exact Fin.elim0 i
      rw [hz]
      exact Matrix.PosSemidef.zero
  | succ n ih =>
      by_cases hnegative : M 0 0 < 0
      · simp [rationalNegativeWitness, hnegative] at hout
      · by_cases hzero : M 0 0 = 0
        · cases hfind : firstNonzeroOffDiagonal M with
          | some j =>
              simp [rationalNegativeWitness, hzero, hfind] at hout
          | none =>
              have hrec : rationalNegativeWitness n (trailingMatrix M) = none := by
                simpa [rationalNegativeWitness, hnegative, hzero, hfind] using hout
              exact KS.W07.fin_psd_of_zero_pivot_tail M hM hzero
                ((firstNonzeroOffDiagonal_none_iff M).mp hfind)
                (ih (trailingMatrix M) (trailingMatrix_isSymm M hM) hrec)
        · have hrec : rationalNegativeWitness n (schurTail M) = none := by
            simpa [rationalNegativeWitness, hnegative, hzero] using hout
          have ha : 0 < M 0 0 :=
            lt_of_le_of_ne (le_of_not_gt hnegative) (Ne.symm hzero)
          exact KS.W07.fin_psd_of_schurTail M hM ha
            (ih (schurTail M) (schurTail_isSymm M hM) hrec)

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem trace_mul_nonneg {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let : CStarAlgebra (Mat d) := {}
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs.isHermitian.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at ht
  exact (Complex.nonneg_iff.mp ht).1

end OperatorNorm

open scoped Matrix.Norms.Frobenius

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

theorem inner_nonneg_of_psd (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    0 ≤ inner ℝ A B := by
  rw [inner_eq_trace]
  exact trace_mul_nonneg hA hB

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InvH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

open scoped Matrix.Norms.L2Operator

theorem inverse_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨u, rfl⟩ := hA.isUnit
  obtain ⟨v, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hab

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

lemma scalar_inv (a : ℝ) : (((a : ℂ) • (1 : Mat d))⁻¹) = (a⁻¹ : ℂ) • (1 : Mat d) := by
  by_cases ha : a = 0
  · simp [ha]
  · let : Invertible (a : ℂ) := invertibleOfNonzero (by exact_mod_cast ha)
    rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv]
    simp

theorem le_trace_smul_one {A : Mat d} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • (1 : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have heig (i : Fin d) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hc : 0 ≤ cfc (fun x : ℝ => A.trace.re - x) A := by
    apply (cfc_nonneg_iff _ A).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hA.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact sub_nonneg.mpr (heig i)
  rw [cfc_sub (fun _ : ℝ => A.trace.re) (fun x : ℝ => x),
    cfc_const _ A hA.isHermitian.isSelfAdjoint] at hc
  change 0 ≤ (algebraMap ℝ (Mat d)) A.trace.re - cfc (id : ℝ → ℝ) A at hc
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint] at hc
  have hmap : (algebraMap ℝ (Mat d)) A.trace.re = (A.trace.re : ℂ) • (1 : Mat d) := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply]
  rw [hmap] at hc
  exact sub_nonneg.mp hc

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalPSDDecision
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17
open Matrix

theorem rationalNegativeWitness_none_iff_psd (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℚ) (hM : M.IsSymm) :
    rationalNegativeWitness n M = none ↔
      (M.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  constructor
  · exact rationalNegativeWitness_none_psd n M hM
  · intro hPSD
    cases ho : rationalNegativeWitness n M with
    | none => rfl
    | some q =>
      have hs := computedPSDSeparator_separates n M hM q ho
      have hn := hs.2 (M.map (fun r : ℚ => (r : ℝ))) hPSD
      exact (not_lt_of_ge hn hs.1).elim

end KS.W17

end

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
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_reaa21f_1 : NormedSpace ℝ (H d) := inferInstance
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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealDecode
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.HermitianCoordinates
open Matrix
open scoped BigOperators

variable {d : ℕ}

lemma realDecode_eq_realify (x : Fin d × Fin d → ℝ) :
    realDecode x = KS.W08.realify (decode x) := by
  ext i j
  cases i <;> cases j <;> rfl

lemma realDecode_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (x : Fin d × Fin d → R) : (realDecode x).map f=realDecode (f ∘ x) := by
  ext i j
  cases i <;> cases j <;>
    simp only [realDecode_inl_inl, realDecode_inl_inr, realDecode_inr_inl, realDecode_inr_inr, Matrix.map_apply,
      Function.comp_def,map_neg]
  all_goals split_ifs <;> simp only [map_neg,map_zero]

lemma realDecode_ratCast (x : Fin d × Fin d → ℚ) :
    (realDecode x).map (fun q => (q:ℝ))=realDecode (fun i => (x i:ℝ)) :=
  realDecode_map (algebraMap ℚ ℝ) x
end CurrentKS.HermitianCoordinates

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ realTrace A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma realTrace_mono {A B : H d} (hab : A ≤ B) : realTrace A ≤ realTrace B := by
  have hh := realTrace_nonneg (show B-A ∈ psdCone d from hab)
  simpa using hh

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma pd_of_lower {a : ℝ} (ha : 0 < a) {A : H d} (hA : a • one ≤ A) : A ∈ pd d := by
  have hp : ((A : Mat d) - (a : ℂ) • 1).PosSemidef := hA
  have hs := (scalar_posDef ha).add_posSemidef hp
  simp only [add_sub_cancel] at hs
  exact hs

lemma inverse_bound_below {a : ℝ} (ha : 0 < a) {A : H d}
    (hA : A ∈ pd d) (he : invH A ≤ a • one) : a⁻¹ • one ≤ A := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  have hi := inverse_antitone hA.inv (scalar_posDef ha) he
  rw [scalar_inv, Matrix.inv_inv_of_invertible] at hi
  change ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d) ≤ (A : Mat d)
  simpa only [Complex.ofReal_inv] using hi

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

lemma scalar_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  exact psd_nonneg (psd_smul one_mem_psdCone (sub_nonneg.mpr hrs))

lemma trace_bound_above {A : H d} (hA : A ∈ psdCone d) : A ≤ realTrace A • one :=
  le_trace_smul_one hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTraceSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → H d) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp only [← inner_one, inner_sum]

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealifyHermitian
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace KS.W08
open Matrix
open scoped ComplexOrder BigOperators

lemma realify_isHermitian_iff {n : Type*} (A : Matrix n n ℂ) :
    (realify A).IsHermitian ↔ A.IsHermitian := by
  refine ⟨?_,realify_isHermitian A⟩
  intro h
  apply realify_injective
  rw [realify_conjTranspose]
  simpa using h.eq

theorem realify_posSemidef_iff {n : Type*} [Fintype n] (A : Matrix n n ℂ) :
    (realify A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((realify_isHermitian_iff A).mp h.isHermitian) ?_
    intro v
    have hv := h.dotProduct_mulVec_nonneg (realifyVector v)
    rw [star_trivial,← realify_mulVec,realifyVector_dotProduct] at hv
    exact Complex.nonneg_iff.mpr ⟨hv,((realify_isHermitian_iff A).mp h.isHermitian |>.im_star_dotProduct_mulVec_self v).symm⟩
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (realify_isHermitian A h.isHermitian) ?_
    intro v
    have hv := h.dotProduct_mulVec_nonneg (complexifyVector v)
    have hr : 0 ≤ (star (complexifyVector v) ⬝ᵥ (A *ᵥ complexifyVector v)).re :=
      Complex.nonneg_iff.mp hv |>.1
    rw [← realifyVector_dotProduct,realify_mulVec,realifyVector_complexify] at hr
    simpa only [star_trivial] using hr

end KS.W08

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

end L2Operator

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Pencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m : ℕ}

lemma Pencil.eval_symmetric (B : Pencil n m) (y : Fin n → ℚ) : (B.eval y).IsSymm := by
  unfold Pencil.eval
  apply Matrix.IsSymm.ext
  intro i j
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [B.symmetric_constant.apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [(B.symmetric_coeff k).apply]

lemma Pencil.cast_eval (B : Pencil n m) (y : Fin n → ℚ) :
    (B.eval y).map (fun x => (x : ℝ)) = B.realEval (fun i => (y i : ℝ)) := by
  ext i j
  simp [Pencil.eval,Pencil.realEval,Matrix.sum_apply,Rat.cast_sum]

lemma Pencil.quadratic_eval (B : Pencil n m) (v : Fin m → ℚ) (y : Fin n → ℚ) :
    KS.W17.psdCutEval v (B.eval y) = B.normal v ⬝ᵥ y - B.offset v := by
  unfold Pencil.normal Pencil.offset
  simp only [KS.W17.psdCutEval,Pencil.eval,Matrix.add_mulVec,
    Matrix.sum_mulVec,Matrix.smul_mulVec,dotProduct_add,dotProduct_sum,dotProduct_smul,
    smul_eq_mul]
  simp only [dotProduct,neg_mul,Finset.sum_neg_distrib]
  rw [show (∑ i, y i * (∑ j,v j*(B.coeff i *ᵥ v) j)) =
      ∑ i, (∑ j,v j*(B.coeff i *ᵥ v) j)*y i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

lemma Pencil.quadratic_realEval (B : Pencil n m) (v : Fin m → ℚ) (y : Fin n → ℝ) :
    KS.W17.psdCutEvalReal v (B.realEval y) =
      (fun i => (B.normal v i : ℝ)) ⬝ᵥ y - (B.offset v : ℝ) := by
  unfold Pencil.realEval
  simp only [KS.W17.psdCutEvalReal,Matrix.add_mulVec,Matrix.sum_mulVec,Matrix.smul_mulVec,
    dotProduct_add,dotProduct_sum,dotProduct_smul,smul_eq_mul]
  have hc : (fun i => (v i : ℝ)) ⬝ᵥ
      (B.constant.map (fun x : ℚ => (x : ℝ)) *ᵥ (fun i => (v i : ℝ))) =
      (B.offset v : ℝ) := by
    simp [Pencil.offset,KS.W17.psdCutEval,dotProduct,Matrix.mulVec,Rat.cast_sum]
  have hi (i : Fin n) : (fun j => (v j : ℝ)) ⬝ᵥ
      ((B.coeff i).map (fun x : ℚ => (x : ℝ)) *ᵥ (fun j => (v j : ℝ))) =
      -(B.normal v i : ℝ) := by
    simp [Pencil.normal,KS.W17.psdCutEval,dotProduct,Matrix.mulVec,Rat.cast_sum]
  rw [hc]
  simp_rw [hi]
  simp only [dotProduct,mul_neg,Finset.sum_neg_distrib]
  rw [show (∑ i, y i * (B.normal v i : ℝ)) = ∑ i, (B.normal v i : ℝ)*y i by
    apply Finset.sum_congr rfl; intro i _; ring]
  ring

lemma Pencil.witness_none_iff (B : Pencil n m) (y : Fin n → ℚ) :
    B.witness y = none ↔ (B.realEval (fun i => (y i : ℝ))).PosSemidef := by
  rw [Pencil.witness,KS.W17.rationalNegativeWitness_none_iff_psd _ _ (B.eval_symmetric y),
    B.cast_eval]

lemma Pencil.witness_some (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) :
    B.offset v < B.normal v ⬝ᵥ y ∧
      ∀ z : Fin n → ℝ, (B.realEval z).PosSemidef →
        (fun i => (B.normal v i : ℝ)) ⬝ᵥ z ≤ (B.offset v : ℝ) := by
  constructor
  · have h := KS.W17.rationalNegativeWitness_sound _ _ (B.eval_symmetric y) v hv
    have h' : 0 < KS.W17.psdCutEval v (B.eval y) := neg_pos.mpr h
    rw [B.quadratic_eval] at h'
    linarith
  · intro z hz
    have h := KS.W17.psdCutEvalReal_nonpos v _ hz
    rw [B.quadratic_realEval] at h
    linarith

lemma Pencil.normal_ne_zero (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) (z : Fin n → ℝ) (hz : (B.realEval z).PosSemidef) :
    B.normal v ≠ 0 := by
  intro hzero
  obtain ⟨h₁,h₂⟩ := B.witness_some y v hv
  have h₂ := h₂ z hz
  rw [hzero,zero_dotProduct] at h₁
  have hzero' : (fun i => (B.normal v i : ℝ)) = 0 := by funext i; simp [hzero]
  rw [hzero',zero_dotProduct] at h₂
  exact (not_lt_of_ge h₂) (by exact_mod_cast h₁)

lemma Pencil.central_cut (B : Pencil n m) (y : Fin n → ℚ) (v : Fin m → ℚ)
    (hv : B.witness y = some v) (z : Fin n → ℝ) (hz : (B.realEval z).PosSemidef) :
    (fun i => (B.normal v i : ℝ)) ⬝ᵥ (z - fun i => (y i : ℝ)) ≤ 0 := by
  obtain ⟨h₁,h₂⟩ := B.witness_some y v hv
  have h₂ := h₂ z hz
  have h₁' : (B.offset v : ℝ) <
      (fun i => (B.normal v i : ℝ)) ⬝ᵥ (fun i => (y i : ℝ)) := by
    simpa [dotProduct,Rat.cast_sum] using (Rat.cast_lt (K := ℝ)).mpr h₁
  rw [dotProduct_sub]
  linarith

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Affine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m p : ℕ}

lemma blockDiagonal_posSemidef (A : Matrix (Fin m) (Fin m) ℝ)
    (B : Matrix (Fin p) (Fin p) ℝ) :
    (blockDiagonal A B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  let C := Matrix.fromBlocks A (0 : Matrix (Fin m) (Fin p) ℝ) 0 B
  have he : (blockDiagonal A B).PosSemidef ↔ C.PosSemidef := by
    constructor
    · intro h
      have hd := h.submatrix (fun i : Fin m ⊕ Fin p => finSumFinEquiv i)
      simp only [blockDiagonal,Matrix.submatrix_submatrix,Function.comp_def,
        Equiv.symm_apply_apply] at hd
      exact hd
    · exact fun h => h.submatrix _
  rw [he]
  constructor
  · intro h
    exact ⟨h.submatrix (Sum.inl : Fin m → Fin m ⊕ Fin p),h.submatrix (Sum.inr : Fin p → Fin m ⊕ Fin p)⟩
  · rintro ⟨hA,hB⟩
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · apply Matrix.isHermitian_fromBlocks_iff.mpr
      exact ⟨hA.isHermitian,by simp,by simp,hB.isHermitian⟩
    · intro x
      have ha := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      have hb := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
      simpa only [C,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,zero_add,
        dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.star_apply,
        star_trivial,Function.comp_def] using add_nonneg ha hb

lemma blockDiagonal_realMap (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin p) (Fin p) ℚ) :
    (blockDiagonal A B).map (fun x => (x:ℝ)) =
      blockDiagonal (A.map (fun x => (x:ℝ))) (B.map (fun x => (x:ℝ))) := by
  ext i j
  change ((Matrix.fromBlocks A 0 0 B) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j):ℝ)=_
  change _=(Matrix.fromBlocks (A.map (fun x => (x:ℝ))) 0 0 (B.map (fun x => (x:ℝ))))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

lemma Pencil.blockDiagonal_realEval (A : Pencil n m) (B : Pencil n p) (z : Fin n → ℝ) :
    (A.blockDiagonal B).realEval z = CurrentKS.RationalSDP.blockDiagonal (A.realEval z) (B.realEval z) := by
  ext i j
  simp only [Pencil.realEval,Pencil.blockDiagonal,blockDiagonal_realMap,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [CurrentKS.RationalSDP.blockDiagonal,hi,hj,Matrix.sum_apply]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_AffineRealEval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators

variable {n m p d N : ℕ}

lemma Pencil.ofAffine_realEval (C : Matrix (Fin m) (Fin m) ℚ)
    (L : (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin m) (Fin m) ℚ)
    (hC : C.IsSymm) (hL : ∀ y,(L y).IsSymm)
    (L' : (Fin n → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (hcast : ∀ y,(L y).map (fun q => (q:ℝ))=L' (fun i => (y i:ℝ))) (y : Fin n → ℝ) :
    (Pencil.ofAffine C L hC hL).realEval y=C.map (fun q => (q:ℝ))+L' y := by
  change _+∑ i,y i • (L (Pi.single i 1)).map (fun q => (q:ℝ))=_
  simp_rw [hcast]
  have hs (i : Fin n) : (fun j => ((Pi.single i 1 : Fin n → ℚ) j:ℝ))=Pi.single i 1 := by
    ext j
    simp [Pi.single_apply,apply_ite]
  simp_rw [hs]
  congr 1
  conv_rhs => rw [vector_eq_sum_single y]
  simp

lemma realFinDecode_cast (x : Fin d × Fin d → ℚ) :
    (realFinDecode d x).map (fun q => (q:ℝ))=realFinDecode d (fun i => (x i:ℝ)) := by
  change ((realDecode x).submatrix _ _).map _=(realDecode _).submatrix _ _
  rw [← Matrix.submatrix_map,realDecode_ratCast]

lemma matrixVariable_cast (second : Bool) (v : Fin (valueDimension d) → ℚ) :
    (matrixVariable d second v).map (fun q => (q:ℝ))=
      matrixVariable d second (fun i => (v i:ℝ)) := by
  change (realFinDecode d _).map _=realFinDecode d _
  rw [realFinDecode_cast]
  rfl

lemma cast_matrix_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin m) (Fin m) ℚ) :
    (∑ i ∈ s,A i).map (fun q => (q:ℝ))=∑ i ∈ s,(A i).map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.sum_apply,Rat.cast_sum]
lemma cast_matrix_smul (r : ℚ) (A : Matrix (Fin m) (Fin m) ℚ) :
    (r • A).map (fun q => (q:ℝ))=(r:ℝ) • A.map (fun q => (q:ℝ)) := by
  ext i j
  simp [Matrix.smul_apply]
lemma cast_matrix_one : (1 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=1 := by
  exact Matrix.map_one _ (by simp) (by simp)
lemma cast_matrix_zero : (0 : Matrix (Fin m) (Fin m) ℚ).map (fun q => (q:ℝ))=0 := by
  ext i j
  simp
lemma cast_matrix_sub (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A-B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))-B.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_neg (A : Matrix (Fin m) (Fin m) ℚ) :
    (-A).map (fun q => (q:ℝ))= -A.map (fun q => (q:ℝ)) := by
  ext i j
  simp
lemma cast_matrix_mul (A B : Matrix (Fin m) (Fin m) ℚ) :
    (A*B).map (fun q => (q:ℝ))=A.map (fun q => (q:ℝ))*B.map (fun q => (q:ℝ)) := by
  exact Matrix.map_mul (f := algebraMap ℚ ℝ)

lemma rationalSum_cast (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ) :
    (rationalSum coords x).map (fun q => (q:ℝ))=
      rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) := by
  simp only [rationalSum,cast_matrix_sum,cast_matrix_smul,realFinDecode_cast]

lemma rationalEta_cast (coords : Fin N → Fin d × Fin d → ℚ) (θ : Fin N → ℚ)
    (Z : Matrix (Fin (d+d)) (Fin (d+d)) ℚ) :
    (rationalEta coords θ Z).map (fun q => (q:ℝ))=
      rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) (Z.map (fun q => (q:ℝ))) := by
  simp only [rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,cast_matrix_sum,
    cast_matrix_smul,sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk,cast_matrix_mul,
    realFinDecode_cast,Rat.cast_mul,Rat.cast_ofNat]

lemma schurPencil_realEval (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (schurPencil coords x θ second).realEval v =
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℝ)+
        (if second then rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
          else -rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))-
        rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) (matrixVariable d (!second) v))
      1 1 (matrixVariable d second v)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  let L' := diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
    (rationalEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ))).comp
      (matrixVariable d (!second))) (matrixVariable d second)
  have hcast (y : Fin (valueDimension d) → ℚ) :
      (diagonalLinear (identityLinear (d+d) (timeCoordinate d)-
        (rationalEta coords θ).comp (matrixVariable d (!second))) (matrixVariable d second) y).map
          (fun q => (q:ℝ))=L' (fun i => (y i:ℝ)) := by
    change (blockDiagonal _ _).map _=blockDiagonal _ _
    rw [blockDiagonal_realMap]
    congr 1
    · change ((timeCoordinate d y : ℚ) • (1 : Matrix (Fin (d+d)) (Fin (d+d)) ℚ)-rationalEta coords θ _).map _=_
      rw [cast_matrix_sub,cast_matrix_smul,cast_matrix_one,rationalEta_cast,matrixVariable_cast]
      rfl
    · exact matrixVariable_cast _ _
  erw [schurPencil,Pencil.ofAffine_realEval _ _ _ _ L' hcast]
  have hS : ((if second then rationalSum coords x else -rationalSum coords x).map
      (fun q => (q:ℝ))) = if second then rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
        else -rationalSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) := by
    split <;> simp only [rationalSum_cast,cast_matrix_neg]
  ext i j
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [L',diagonalLinear,blockDiagonal,hi,hj,identityLinear,Matrix.add_apply,Matrix.sub_apply]
  · rename_i i' j'
    have hs := congrFun (congrFun hS i') j'
    change ((if second=true then rationalSum coords x else -rationalSum coords x) _ _ : ℝ)=_ at hs
    rw [hs]
    abel
  · simp [Matrix.one_apply,apply_ite]
  · simp [Matrix.one_apply,apply_ite]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_BlockScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix
open scoped BigOperators

variable {n m : ℕ}

lemma blockScalar_posSemidef (A : Matrix (Fin m) (Fin m) ℝ) (b : ℝ) :
    (blockScalar A b).PosSemidef ↔ A.PosSemidef ∧ 0 ≤ b := by
  let C := Matrix.fromBlocks A (0 : Matrix (Fin m) (Fin 1) ℝ) 0 (Matrix.of fun (_ _ : Fin 1) => b)
  have he : (blockScalar A b).PosSemidef ↔ C.PosSemidef := by
    constructor
    · intro h
      have hd := h.submatrix (fun i : Fin m ⊕ Fin 1 => finSumFinEquiv i)
      simp only [blockScalar,Matrix.submatrix_submatrix,Function.comp_def,
        Equiv.symm_apply_apply] at hd
      exact hd
    · exact fun h => h.submatrix _
  rw [he]
  constructor
  · intro h
    have hA := h.submatrix (Sum.inl : Fin m → Fin m ⊕ Fin 1)
    have hb := h.submatrix (Sum.inr : Fin 1 → Fin m ⊕ Fin 1)
    refine ⟨by simp only [C,Matrix.submatrix,Matrix.fromBlocks_apply₁₁] at hA; exact hA,?_⟩
    have hh := hb.diag_nonneg (i := (0 : Fin 1))
    exact hh
  · rintro ⟨hA,hb⟩
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_,?_⟩
    · apply Matrix.isHermitian_fromBlocks_iff.mpr
      exact ⟨hA.isHermitian,by simp,by simp,by ext i j; simp⟩
    · intro x
      have hh := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
      simp only [dotProduct,Pi.star_apply,star_trivial,Function.comp_def] at hh
      change 0 ≤ ∑ i : Fin m, x (Sum.inl i)*(A *ᵥ (x ∘ Sum.inl)) i at hh
      have hs : 0 ≤ b*(x (Sum.inr 0))^2 := mul_nonneg hb (sq_nonneg _)
      simpa only [C,Matrix.fromBlocks_mulVec,Matrix.zero_mulVec,add_zero,zero_add,
        dotProduct, Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Pi.star_apply,star_trivial,
        Function.comp_def,Matrix.mulVec,Fin.sum_univ_one,Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply,Matrix.of_apply,zero_mul,Finset.sum_const_zero] using show
          0 ≤ (∑ i : Fin m, x (Sum.inl i)*(A *ᵥ (x ∘ Sum.inl)) i)+
            x (Sum.inr 0)*(b*x (Sum.inr 0)) by nlinarith

lemma blockScalar_realMap (A : Matrix (Fin m) (Fin m) ℚ) (b : ℚ) :
    (blockScalar A b).map (fun x => (x:ℝ)) =
      blockScalar (A.map (fun x => (x:ℝ))) (b:ℝ) := by
  ext i j
  change ((Matrix.fromBlocks A 0 0 (Matrix.of fun (_ _ : Fin 1) => b))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) : ℝ) = _
  change _ = (Matrix.fromBlocks (A.map (fun x => (x:ℝ))) 0 0 (Matrix.of fun (_ _ : Fin 1) => (b:ℝ)))
    (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp

lemma Pencil.withLevel_realEval (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ) (z : Fin n → ℝ) :
    (B.withLevel f q).realEval z =
      blockScalar (B.realEval z) ((q:ℝ)-(fun i => (f i:ℝ)) ⬝ᵥ z) := by
  ext i j
  simp only [Pencil.realEval,Pencil.withLevel,blockScalar_realMap,
    Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
    simp [blockScalar,hi,hj,Matrix.sum_apply,dotProduct,mul_comm,sub_eq_add_neg]

lemma Pencil.withLevel_feasible (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ)
    (z : EuclideanSpace ℝ (Fin n)) :
    ((B.withLevel f q).realEval z).PosSemidef ↔ (B.realEval z).PosSemidef ∧
      (fun i => (f i:ℝ)) ⬝ᵥ z ≤ (q:ℝ) := by
  rw [B.withLevel_realEval,blockScalar_posSemidef,sub_nonneg]
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FinRealify
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates KS.W08
open scoped BigOperators ComplexOrder

variable {n m p d N : ℕ}

lemma lowerMatrixPencil_realEval (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (lowerMatrixPencil d second).realEval v = matrixVariable d second v-(1/400:ℝ) • 1 := by
  rw [lowerMatrixPencil,Pencil.ofAffine_realEval _ _ _ _ (matrixVariable d second)
    (matrixVariable_cast second),cast_matrix_smul,cast_matrix_one]
  norm_num
  abel
lemma upperMatrixPencil_realEval (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    (upperMatrixPencil d ε second).realEval v = (200/(ε:ℝ)) • 1-matrixVariable d second v := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      ((-(matrixVariable (R := ℚ) d second)) y).map (fun q => (q:ℝ))=
        (-(matrixVariable (R := ℝ) d second)) (fun i => (y i:ℝ)) := by
    simp only [LinearMap.neg_apply,cast_matrix_neg,matrixVariable_cast]
  erw [upperMatrixPencil,Pencil.ofAffine_realEval _ _ _ _ (-(matrixVariable (R := ℝ) d second)) hc,
    cast_matrix_smul,cast_matrix_one]
  simp only [Rat.cast_div,Rat.cast_ofNat,LinearMap.neg_apply,sub_eq_add_neg]
lemma lowerTimePencil_realEval (v : Fin (valueDimension d) → ℝ) :
    (lowerTimePencil d).realEval v=timeCoordinate d v • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      (identityLinear 1 (timeCoordinate d) y).map (fun q => (q:ℝ))=
        identityLinear 1 (timeCoordinate d) (fun i => (y i:ℝ)) := by
    change ((timeCoordinate d y : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ)).map _=_
    rw [cast_matrix_smul,cast_matrix_one]
    rfl
  erw [lowerTimePencil,Pencil.ofAffine_realEval _ _ _ _ (identityLinear 1 (timeCoordinate d)) hc,
    cast_matrix_zero,zero_add]
  rfl
lemma upperTimePencil_realEval (v : Fin (valueDimension d) → ℝ) :
    (upperTimePencil d).realEval v=(100-timeCoordinate d v) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hc (y : Fin (valueDimension d) → ℚ) :
      ((-(identityLinear (R := ℚ) 1 (timeCoordinate d))) y).map (fun q => (q:ℝ))=
        (-(identityLinear (R := ℝ) 1 (timeCoordinate d))) (fun i => (y i:ℝ)) := by
    change (-((timeCoordinate d y : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ))).map _=_
    rw [cast_matrix_neg,cast_matrix_smul,cast_matrix_one]
    rfl
  erw [upperTimePencil,Pencil.ofAffine_realEval _ _ _ _ (-(identityLinear (R := ℝ) 1 (timeCoordinate d))) hc,
    cast_matrix_smul,cast_matrix_one]
  norm_num only [Rat.cast_ofNat]
  change (100:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) + -(timeCoordinate d v • 1)=_
  module

lemma posSemidef_reindex_iff {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℝ) (e : β ≃ α) : (A.submatrix e e).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro h
    have hh := h.submatrix e.symm
    simp only [Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply] at hh
    exact hh
  · exact fun h => h.submatrix _

lemma finRealify_psd (A : Matrix (Fin d) (Fin d) ℂ) :
    (finRealify A).PosSemidef ↔ A.PosSemidef := by
  rw [finRealify,posSemidef_reindex_iff,realify_posSemidef_iff]
lemma finRealify_decode (x : Fin d × Fin d → ℝ) : finRealify (decode x)=realFinDecode d x := by
  unfold finRealify
  rw [← realDecode_eq_realify]
  rfl
lemma finRealify_one : finRealify (1 : Matrix (Fin d) (Fin d) ℂ)=1 := by
  unfold finRealify
  rw [realify_one]
  ext i j
  simp [Matrix.one_apply]
lemma finRealify_add (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A+B)=finRealify A+finRealify B := by
  simp only [finRealify,realify_add,Matrix.submatrix_add,Pi.add_apply]
lemma finRealify_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (r • A)=r • finRealify A := by
  simp only [finRealify,realify_smul,Matrix.submatrix_smul,Pi.smul_apply]
lemma finRealify_neg (A : Matrix (Fin d) (Fin d) ℂ) : finRealify (-A)= -finRealify A := by
  have h : realify (-A) = -realify A := by
    ext (i|i) (j|j) <;> simp [realify,Matrix.fromBlocks]
  simp only [finRealify,h,Matrix.submatrix_neg]
  rfl
lemma finRealify_sub (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A-B)=finRealify A-finRealify B := by
  simp only [sub_eq_add_neg,finRealify_add,finRealify_neg]
lemma finRealify_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (A*B)=finRealify A*finRealify B := by
  rw [finRealify,realify_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv.symm _).symm
lemma finRealify_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    finRealify (∑ i ∈ s,A i)=∑ i ∈ s,finRealify (A i) := by
  ext i j
  simp only [finRealify,realify_sum,Matrix.submatrix_apply,Matrix.sum_apply]

lemma realify_schur (T X : Matrix (Fin d) (Fin d) ℂ) :
    (realify (Matrix.fromBlocks T 1 1 X)).submatrix
      (Equiv.sumSumSumComm (Fin d) (Fin d) (Fin d) (Fin d))
      (Equiv.sumSumSumComm (Fin d) (Fin d) (Fin d) (Fin d))=
    Matrix.fromBlocks (realify T) 1 1 (realify X) := by
  ext i j
  rcases i with i | i <;> rcases i with i | i <;>
    rcases j with j | j <;> rcases j with j | j <;>
    simp [realify,Matrix.fromBlocks,Equiv.sumSumSumComm,Matrix.one_apply,apply_ite]

lemma finRealify_schur_psd (T X : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.fromBlocks (finRealify T) 1 1 (finRealify X)).PosSemidef ↔
      (Matrix.fromBlocks T (1 : Matrix (Fin d) (Fin d) ℂ) 1 X).PosSemidef := by
  let e := (finSumFinEquiv.symm : Fin (d+d) ≃ Fin d ⊕ Fin d).sumCongr
    (finSumFinEquiv.symm : Fin (d+d) ≃ Fin d ⊕ Fin d)
  have he : Matrix.fromBlocks (finRealify T) 1 1 (finRealify X)=
      (Matrix.fromBlocks (realify T) 1 1 (realify X)).submatrix e e := by
    ext i j
    cases i <;> cases j <;> simp [finRealify,e,Matrix.one_apply]
  rw [he,posSemidef_reindex_iff,← realify_schur,posSemidef_reindex_iff,realify_posSemidef_iff]

lemma finRealify_complexSum (coords : Fin N → Fin d × Fin d → ℝ) (x : Fin N → ℝ) :
    finRealify (complexSum coords x)=rationalSum coords x := by
  simp only [complexSum,finRealify_sum,finRealify_smul,finRealify_decode,rationalSum]
lemma finRealify_complexEta (coords : Fin N → Fin d × Fin d → ℝ) (θ : Fin N → ℝ)
    (Z : Matrix (Fin d) (Fin d) ℂ) :
    finRealify (complexEta coords θ Z)=rationalEta coords θ (finRealify Z) := by
  simp only [complexEta,finRealify_sum,finRealify_smul,finRealify_mul,finRealify_decode,
    rationalEta,LinearMap.sum_apply,LinearMap.smul_apply,sandwichLinear,LinearMap.coe_mk,AddHom.coe_mk]

lemma schurPencil_psd (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((schurPencil coords x θ second).realEval v).PosSemidef ↔
    (Matrix.fromBlocks
      (timeCoordinate d v • (1 : Matrix (Fin d) (Fin d) ℂ)+
        (if second then complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ))
          else -complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))-
        complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ))
          (decode (matrixCoordinate d (!second) v)))
      1 1 (decode (matrixCoordinate d second v))).PosSemidef := by
  rw [schurPencil_realEval,posSemidef_reindex_iff,← finRealify_schur_psd]
  simp only [finRealify_sub,finRealify_add,finRealify_smul,finRealify_one,
    finRealify_complexEta,finRealify_decode]
  split <;> simp only [finRealify_complexSum,finRealify_neg,matrixVariable,LinearMap.comp_apply]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ComplexValueProgram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open Matrix CurrentKS.HermitianCoordinates
open scoped BigOperators ComplexOrder

variable {d N : ℕ}

lemma scalar_one_psd_iff (r : ℝ) :
    (r • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef ↔ 0 ≤ r := by
  constructor
  · intro h
    simpa using h.diag_nonneg (i := (0 : Fin 1))
  · intro hr
    exact (Matrix.PosSemidef.one : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef).smul hr

lemma lowerMatrixPencil_psd (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((lowerMatrixPencil d second).realEval v).PosSemidef ↔
    (decode (matrixCoordinate d second v)-(1/400:ℝ) •
      (1 : Matrix (Fin d) (Fin d) ℂ)).PosSemidef := by
  rw [lowerMatrixPencil_realEval,← finRealify_psd]
  simp only [finRealify_sub,finRealify_smul,finRealify_one,finRealify_decode,
    matrixVariable,LinearMap.comp_apply]
lemma upperMatrixPencil_psd (ε : ℚ) (second : Bool) (v : Fin (valueDimension d) → ℝ) :
    ((upperMatrixPencil d ε second).realEval v).PosSemidef ↔
    ((200/(ε:ℝ)) • (1 : Matrix (Fin d) (Fin d) ℂ)-
      decode (matrixCoordinate d second v)).PosSemidef := by
  rw [upperMatrixPencil_realEval,← finRealify_psd]
  simp only [finRealify_sub,finRealify_smul,finRealify_one,finRealify_decode,
    matrixVariable,LinearMap.comp_apply]

lemma valuePencil_psd (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ε : ℚ) (v : Fin (valueDimension d) → ℝ) :
    ((valuePencil coords x θ ε).realEval v).PosSemidef ↔
    complexValueProgram (ε:ℝ)
      (complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)))
      (complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)))
      (timeCoordinate d v) (decode (matrixCoordinate d false v))
      (decode (matrixCoordinate d true v)) := by
  simp only [valuePencil,Pencil.blockDiagonal_realEval,blockDiagonal_posSemidef,
    schurPencil_psd,lowerMatrixPencil_psd,upperMatrixPencil_psd,
    lowerTimePencil_realEval,upperTimePencil_realEval,scalar_one_psd_iff,
    Bool.false_eq_true,ite_false, if_false,Bool.not_false,ite_true, if_true,Bool.not_true,
    complexValueProgram,sub_eq_add_neg]
  simp only [← sub_eq_add_neg,sub_nonneg]
  tauto

lemma trace_decode (x : Fin d × Fin d → ℝ) :
    (Matrix.trace (decode x)).re=∑ i,x (i,i) := by
  simp [Matrix.trace,decode]

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealVector
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ≤ ∑ i, |v i| := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => abs_nonneg _))).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => |v i|) (fun i _ => abs_nonneg _)

lemma l1_bounds (a : Fin n → ℚ) :
    ‖realVector a‖ ≤ (l1 a : ℝ) ∧ (l1 a : ℝ) ≤ (n+1 : ℝ)*‖realVector a‖ := by
  have hcast : (l1 a : ℝ) = ∑ i, |realVector a i| := by
    simp [l1,realVector,Rat.cast_sum]
  rw [hcast]
  refine ⟨norm_le_sum_abs _,?_⟩
  calc
    _ ≤ ∑ _i : Fin n, ‖realVector a‖ := Finset.sum_le_sum (fun i _ => by
      simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (realVector a) i))
    _ = (n : ℝ)*‖realVector a‖ := by simp
    _ ≤ _ := by nlinarith [norm_nonneg (realVector a)]

lemma l1_pos {a : Fin n → ℚ} (ha : a ≠ 0) : 0 < l1 a := by
  have ha' : realVector a ≠ 0 := by
    intro h
    apply ha
    funext i
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x i) h
    simp only [realVector,PiLp.toLp_apply,PiLp.zero_apply,Rat.cast_eq_zero] at hh
    exact hh
  have hp := norm_pos_iff.mpr ha'
  exact_mod_cast lt_of_lt_of_le hp (l1_bounds a).1

lemma roundScalar_error (ρ x : ℚ) (hρ : 0 < ρ) : |roundScalar ρ x-x| ≤ ρ := by
  have h₁ := Int.floor_le (x/ρ)
  have h₂ := Int.lt_floor_add_one (x/ρ)
  have hlow : roundScalar ρ x ≤ x := by
    dsimp [roundScalar]
    have := mul_le_mul_of_nonneg_left h₁ hρ.le
    rwa [mul_div_cancel₀ _ hρ.ne'] at this
  have hhigh : x < roundScalar ρ x+ρ := by
    dsimp [roundScalar]
    have := mul_lt_mul_of_pos_left h₂ hρ
    rw [mul_div_cancel₀ _ hρ.ne'] at this
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlow)]
  linarith

lemma realVector_round_error (ρ : ℚ) (hρ : 0 < ρ) (y : Fin n → ℚ) :
    ‖realVector (roundVector ρ y)-realVector y‖ ≤ (n+1 : ℝ)*(ρ : ℝ) := by
  calc
    _ ≤ ∑ i, |(realVector (roundVector ρ y)-realVector y) i| := norm_le_sum_abs _
    _ ≤ ∑ _i : Fin n, (ρ : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := roundScalar_error ρ (y i) hρ
      simpa only [realVector,roundVector,PiLp.sub_apply,PiLp.toLp_apply,Rat.cast_sub,
        Rat.cast_abs] using (Rat.cast_le (K := ℝ)).mpr h
    _ = (n : ℝ)*(ρ : ℝ) := by simp
    _ ≤ _ := by
      have hp : 0 < (ρ : ℝ) := by exact_mod_cast hρ
      nlinarith

lemma normalized_norm_le_one (a : Fin n → ℚ) : ‖normalized a‖ ≤ 1 := by
  by_cases ha : a=0
  · simp [normalized,l1,ha,realVector]
  have hq : 0 < (l1 a : ℝ) := by exact_mod_cast l1_pos ha
  rw [normalized,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hq]
  exact (inv_mul_le_iff₀ hq).mpr (by simpa only [mul_one] using (l1_bounds a).1)

lemma normalized_margin (K : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (y a : Fin n → ℚ) {r : ℝ} (hr : 0 ≤ r) (ha : a ≠ 0)
    (hball : Metric.closedBall c r ⊆ K)
    (hsep : ∀ z ∈ K, inner ℝ (realVector a) (z-realVector y) ≤ 0) :
    r/(n+1) ≤ inner ℝ (normalized a) (c-realVector y) := by
  have hq : 0 < (l1 a : ℝ) := by exact_mod_cast l1_pos ha
  have ha0 : realVector a ≠ 0 := by
    intro h
    have han := (l1_bounds a).2
    rw [h,norm_zero,mul_zero] at han
    linarith
  have hnorm : 0 < ‖realVector a‖ := norm_pos_iff.mpr ha0
  let v := (-‖realVector a‖⁻¹) • realVector a
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
  have hsep' : ∀ z ∈ K, inner ℝ v (realVector y) ≤ inner ℝ v z := by
    intro z hz
    have hh := hsep z hz
    rw [inner_sub_right] at hh
    dsimp [v]
    rw [real_inner_smul_left,real_inner_smul_left]
    exact mul_le_mul_of_nonpos_left (by linarith) (neg_nonpos.mpr (inv_nonneg.mpr hnorm.le))
  have hm := CurrentKS.RationalOptimization.separating_margin K c (realVector y) v hr hball hv hsep' le_rfl
  have hn : normalized a = (‖realVector a‖/(l1 a : ℝ)) • v := by
    dsimp [normalized,v]
    rw [smul_smul]
    congr 1
    field_simp
  rw [hn,real_inner_smul_left]
  have hrn : (1 : ℝ)/(n+1) ≤ ‖realVector a‖/(l1 a : ℝ) := by
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<n+1) hq).mpr
    simpa only [one_mul,mul_comm] using (l1_bounds a).2
  calc
    r/(n+1) = ((1:ℝ)/(n+1))*r := by ring
    _ ≤ (‖realVector a‖/(l1 a : ℝ))*inner ℝ v (c-realVector y) :=
      mul_le_mul hrn hm hr (div_nonneg hnorm.le hq.le)

lemma realVector_step (y a : Fin n → ℚ) (step : ℚ) :
    realVector (fun i => y i-step*a i/l1 a) = realVector y+(step : ℝ) • normalized a := by
  ext i
  simp [realVector,normalized,Rat.cast_sub,Rat.cast_mul,div_eq_mul_inv]
  ring

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Feasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma Pencil.next_eq_self (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (hy : B.witness y=none) : B.next step mesh y=y := by simp [Pencil.next,hy]

lemma Pencil.next_decrease (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hstep : (step : ℝ)=r/(n+1))
    (hball : Metric.closedBall c r ⊆ B.feasible)
    (hsmall : 2*(R+step)*((n+1)*mesh)+((n+1)*mesh)^2 ≤ (step : ℝ)^2/2)
    (hy : ‖realVector y-c‖ ≤ R) (hfail : B.witness y ≠ none) :
    ‖realVector (B.next step mesh y)-c‖^2 ≤ ‖realVector y-c‖^2-(step : ℝ)^2/2 := by
  obtain ⟨v,hv⟩ := Option.ne_none_iff_exists'.mp hfail
  have hc : c ∈ B.feasible := hball (Metric.mem_closedBall_self hr.le)
  have ha := B.normal_ne_zero y v hv c hc
  have hm := normalized_margin B.feasible c y (B.normal v) hr.le ha hball
    (fun z hz => by
      have h := B.central_cut y v hv z hz
      change (∑ i : Fin n, (z i-(y i : ℝ))*(B.normal v i : ℝ)) ≤ 0
      simpa only [dotProduct,Pi.sub_apply,mul_comm] using h)
  have hround := realVector_round_error mesh hmesh
    (fun i => y i-step*B.normal v i/l1 (B.normal v))
  rw [realVector_step] at hround
  have hp : 0 ≤ (step : ℝ) := by rw [hstep]; positivity
  have hδ : 0 ≤ (n+1 : ℝ)*(mesh : ℝ) := by positivity
  rw [Pencil.next,hv]
  exact CurrentKS.RationalOptimization.rounded_step_decrease _ c _ _ hp hR hδ hy
    (normalized_norm_le_one _) (hstep ▸ hm) hround hsmall

theorem Pencil.search_feasible (B : Pencil n m) (step mesh : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (hstep : (step : ℝ)=r/(n+1))
    (hball : Metric.closedBall c r ⊆ B.feasible)
    (hsmall : 2*(R+step)*((n+1)*mesh)+((n+1)*mesh)^2 ≤ (step : ℝ)^2/2)
    (hy : ‖realVector y-c‖ ≤ R) (T : ℕ) (hT : R^2 < T*(step : ℝ)^2/2) :
    B.witness ((B.next step mesh)^[T] y)=none := by
  have hp : 0 < (step : ℝ) := by rw [hstep]; positivity
  have hbound : ∀ k : ℕ,
      B.witness ((B.next step mesh)^[k] y)=none ∨
      ‖realVector ((B.next step mesh)^[k] y)-c‖^2 ≤ R^2-k*(step : ℝ)^2/2 := by
    intro k
    induction k with
    | zero =>
      right
      simpa using (sq_le_sq₀ (norm_nonneg _) hR).mpr hy
    | succ k ih =>
      rcases ih with hh|hh
      · left
        rw [Function.iterate_succ_apply',B.next_eq_self _ _ _ hh]
        exact hh
      · by_cases ha : B.witness ((B.next step mesh)^[k] y)=none
        · left
          rw [Function.iterate_succ_apply',B.next_eq_self _ _ _ ha]
          exact ha
        · right
          have hdist : ‖realVector ((B.next step mesh)^[k] y)-c‖ ≤ R := by
            apply (sq_le_sq₀ (norm_nonneg _) hR).mp
            calc
              _ ≤ R^2-k*(step : ℝ)^2/2 := hh
              _ ≤ R^2 := sub_le_self _ (by positivity)
          have hd := B.next_decrease step mesh ((B.next step mesh)^[k] y) c hr hR hmesh
            hstep hball hsmall hdist ha
          rw [Function.iterate_succ_apply']
          push_cast
          linarith
  rcases hbound T with h|h
  · exact h
  · have hn := sq_nonneg ‖realVector ((B.next step mesh)^[T] y)-c‖
    linarith

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SearchStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma searchStep_pos {r : ℚ} (hr : 0 < r) : 0 < searchStep n r := by
  unfold searchStep
  positivity

lemma searchMesh_pos {r R : ℚ} (hr : 0 < r) (hR : 0 ≤ R) : 0 < searchMesh n r R := by
  have hs := searchStep_pos (n := n) hr
  unfold searchMesh
  positivity

lemma mesh_error_small {s R : ℝ} (hs : 0 < s) (_hs1 : s ≤ 1) (hR : 0 ≤ R) :
    2*(R+s)*(s^2/(16*(R+s+1)))+(s^2/(16*(R+s+1)))^2 ≤ s^2/2 := by
  have hden : 0 < 16*(R+s+1) := by positivity
  have hδ : 0 ≤ s^2/(16*(R+s+1)) := by positivity
  have hfirst : 2*(R+s)*(s^2/(16*(R+s+1))) ≤ s^2/8 := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<8)).mpr
    nlinarith [sq_nonneg s]
  have hδs : s^2/(16*(R+s+1)) ≤ s/16 := by
    apply (div_le_div_iff₀ hden (by norm_num : (0:ℝ)<16)).mpr
    nlinarith [mul_nonneg hs.le hR]
  have hδsq := pow_le_pow_left₀ hδ hδs 2
  nlinarith [sq_nonneg s]

lemma searchMesh_small {r R : ℚ} (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) :
    2*((R : ℝ)+searchStep n r)*((n+1)*(searchMesh n r R : ℝ))+
      ((n+1)*(searchMesh n r R : ℝ))^2 ≤ (searchStep n r : ℝ)^2/2 := by
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hs : 0 < (searchStep n r : ℝ) := by exact_mod_cast searchStep_pos (n := n) hr
  have hs1' : searchStep n r ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℚ)<n+1)).mpr
    exact hr1.trans (le_add_of_nonneg_left (Nat.cast_nonneg n))
  have hs1 : (searchStep n r : ℝ) ≤ 1 := by exact_mod_cast hs1'
  have hR' : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have he : (n+1)*(searchMesh n r R : ℝ) =
      (searchStep n r : ℝ)^2/(16*((R:ℝ)+searchStep n r+1)) := by
    simp only [searchMesh,Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_add,
      Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one]
    field_simp
  rw [he]
  exact mesh_error_small hs hs1 hR'

lemma searchFuel_suffices {r R : ℚ} (hr : 0 < r) (_hR : 0 ≤ R) :
    (R:ℝ)^2 < (searchFuel n r R : ℝ)*(searchStep n r : ℝ)^2/2 := by
  have hs : 0 < searchStep n r := searchStep_pos hr
  have hc := Nat.le_ceil (4*R^2/(searchStep n r)^2)
  have hh : 2*R^2/(searchStep n r)^2 < (searchFuel n r R : ℚ) := by
    unfold searchFuel
    push_cast
    have := div_nonneg (sq_nonneg R) (sq_nonneg (searchStep n r))
    simp only [mul_div_assoc] at hc ⊢
    linarith
  have hmul := (div_lt_iff₀ (pow_pos hs 2)).mp hh
  have hcast : 2*(R:ℝ)^2 < (searchFuel n r R : ℝ)*(searchStep n r : ℝ)^2 := by
    exact_mod_cast hmul
  linarith

theorem Pencil.search_accepts (B : Pencil n m) (r R : ℚ) (y : Fin n → ℚ)
    (c : EuclideanSpace ℝ (Fin n)) (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R)
    (hball : Metric.closedBall c (r:ℝ) ⊆ B.feasible)
    (hy : ‖realVector y-c‖ ≤ (R:ℝ)) :
    B.witness (B.search r R y)=none := by
  apply B.search_feasible (searchStep n r) (searchMesh n r R) y c
    (by exact_mod_cast hr) (by exact_mod_cast hR) (searchMesh_pos hr hR)
    (by simp [searchStep]) hball (searchMesh_small hr hr1 hR) hy
    (searchFuel n r R) (searchFuel_suffices hr hR)

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Level
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma Pencil.witness_withLevel (B : Pencil n m) (f : Fin n → ℚ) (q : ℚ) (y : Fin n → ℚ) :
    (B.withLevel f q).witness y = none ↔
      realVector y ∈ B.feasible ∧ (fun i => (f i:ℝ)) ⬝ᵥ realVector y ≤ (q:ℝ) := by
  rw [Pencil.witness_none_iff]
  change realVector y ∈ (B.withLevel f q).feasible ↔ _
  exact B.withLevel_feasible f q (realVector y)

lemma level_mono {δ U : ℚ} (hδ : 0 ≤ δ) : Monotone (level δ U) := by
  intro k l hkl
  unfold level
  exact add_le_add (le_refl (-U)) (mul_le_mul_of_nonneg_right (show (k:ℚ) ≤ (l:ℚ) by exact_mod_cast hkl) hδ)

lemma Pencil.optimize_preserves (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (hδ : 0 ≤ δ) {k l : ℕ} (hkl : k ≤ l)
    (hk : (B.withLevel f (level δ U k)).witness (B.optimize f δ r R U k)=none) :
    B.optimize f δ r R U l = B.optimize f δ r R U k := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hl : (B.withLevel f (level δ U l)).witness (B.optimize f δ r R U l)=none := by
      rw [ih,B.witness_withLevel]
      obtain ⟨hm,ho⟩ := (B.witness_withLevel _ _ _).mp hk
      refine ⟨hm,ho.trans ?_⟩
      exact_mod_cast level_mono hδ hkl
    rw [Pencil.optimize,ite_eq_left hl,ih]

lemma Pencil.optimize_accepts (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (hδ : 0 ≤ δ) (k : ℕ)
    (hk : (B.withLevel f (level δ U k)).witness (B.levelCandidate f δ r R U k)=none) :
    (B.withLevel f (level δ U k)).witness (B.optimize f δ r R U k)=none := by
  cases k with
  | zero => exact hk
  | succ k =>
    by_cases h : (B.withLevel f (level δ U k)).witness (B.optimize f δ r R U k)=none
    · simp only [Pencil.optimize,h,ite_true, if_true]
      rw [B.witness_withLevel] at h ⊢
      refine ⟨h.1,h.2.trans ?_⟩
      exact_mod_cast level_mono hδ (Nat.le_succ k)
    · simpa only [Pencil.optimize,h,ite_false, if_false] using hk

theorem Pencil.optimize_bound (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (hδ : 0 ≤ δ) {k K : ℕ} (hkK : k ≤ K)
    (hk : (B.withLevel f (level δ U k)).witness (B.levelCandidate f δ r R U k)=none) :
    realVector (B.optimize f δ r R U K) ∈ B.feasible ∧
      (fun i => (f i:ℝ)) ⬝ᵥ realVector (B.optimize f δ r R U K) ≤ (level δ U k:ℝ) := by
  have ha := B.optimize_accepts f δ r R U hδ k hk
  rw [B.optimize_preserves f δ r R U hδ hkK ha]
  exact (B.witness_withLevel _ _ _).mp ha

lemma Pencil.levelCandidate_accepts (B : Pencil n m) (f : Fin n → ℚ) (δ r R U : ℚ)
    (k : ℕ) (c : EuclideanSpace ℝ (Fin n)) (hr : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R)
    (hc : ‖c‖ ≤ (R:ℝ))
    (hball : Metric.closedBall c (r:ℝ) ⊆
      B.feasible ∩ {y | (fun i => (f i:ℝ)) ⬝ᵥ y ≤ (level δ U k:ℝ)}) :
    (B.withLevel f (level δ U k)).witness (B.levelCandidate f δ r R U k)=none := by
  apply Pencil.search_accepts _ _ _ _ c hr hr1 hR
  · intro y hy
    exact (B.withLevel_feasible f _ y).mpr (hball hy)
  · have hz : realVector (0 : Fin n → ℚ)=0 := by ext i; simp [realVector]
    simpa only [hz,zero_sub,norm_neg] using hc

end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ObjectiveCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open scoped BigOperators RealInnerProductSpace
open Set

variable {n m : ℕ}

lemma Pencil.realEval_convex (B : Pencil n m) (x y : Fin n → ℝ) (a b : ℝ)
    (hab : a+b=1) : B.realEval (a • x+b • y) = a • B.realEval x+b • B.realEval y := by
  ext i j
  simp only [Pencil.realEval,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,Pi.add_apply,Pi.smul_apply]
  simp only [mul_add,Finset.mul_sum,add_mul,mul_assoc]
  rw [Finset.sum_add_distrib]
  have h := congrArg (fun t : ℝ => t * (B.constant.map (fun q : ℚ => (q : ℝ)) i j)) hab
  nlinarith [h]

lemma Pencil.convex_feasible (B : Pencil n m) : Convex ℝ B.feasible := by
  intro x hx y hy a b ha hb hab
  change (B.realEval (a • x+b • y)).PosSemidef
  rw [B.realEval_convex x y a b hab]
  exact (hx.smul ha).add (hy.smul hb)

lemma objectiveCLM_apply (f : Fin n → ℚ) (y : EuclideanSpace ℝ (Fin n)) :
    objectiveCLM f y = (fun i => (f i:ℝ)) ⬝ᵥ y := by
  change (∑ i, y i * (f i:ℝ)) = ∑ i, (f i:ℝ)*y i
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma norm_convexCombination_le (z c : EuclideanSpace ℝ (Fin n)) {a R : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hz : ‖z‖ ≤ R) (hc : ‖c‖ ≤ R) :
    ‖(1-a) • z+a • c‖ ≤ R := by
  calc
    _ ≤ ‖(1-a) • z‖+‖a • c‖ := norm_add_le _ _
    _ = (1-a)*‖z‖+a*‖c‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg ha,abs_of_nonneg (sub_nonneg.mpr ha1)]
    _ ≤ (1-a)*R+a*R := add_le_add (mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr ha1))
      (mul_le_mul_of_nonneg_left hc ha)
    _ = R := by ring

lemma nearRadius_pos {δ L R r : ℚ} (hδ : 0 < δ) (hL : 0 < L)
    (hR : 0 ≤ R) (hr : 0 < r) : 0 < nearRadius δ L R r := by
  unfold nearRadius
  positivity

lemma nearRadius_le {δ L R r : ℚ} (hL : 0 < L) (hR : 0 ≤ R) (hr : 0 < r)
    (hδsmall : δ ≤ L*(2*R+r)) : nearRadius δ L R r ≤ r := by
  have hd : (0:ℚ) < L*(2*R+r) := by positivity
  exact (mul_le_mul_of_nonneg_right ((div_le_one hd).mpr hδsmall) hr.le).trans_eq (one_mul r)

lemma exists_near_level {δ U v : ℝ} (hδ : 0 < δ) (hv : -U ≤ v) (hvU : v ≤ U) :
    ∃ k : ℕ, k ≤ ⌈2*U/δ⌉₊+3 ∧ v+δ ≤ -U+k*δ ∧ -U+k*δ ≤ v+2*δ := by
  let k : ℕ := ⌈(v+U)/δ⌉₊+1
  have hratio : 0 ≤ (v+U)/δ := div_nonneg (by linarith) hδ.le
  have hc := Nat.le_ceil ((v+U)/δ)
  have hlt := Nat.ceil_lt_add_one hratio
  refine ⟨k,?_,?_,?_⟩
  · have hm : (v+U)/δ ≤ 2*U/δ := div_le_div_of_nonneg_right (by linarith) hδ.le
    have hh := Nat.ceil_mono hm
    dsimp [k]
    omega
  · have hh := (div_le_iff₀ hδ).mp hc
    dsimp [k]
    push_cast
    nlinarith
  · have hh := (lt_div_iff₀ hδ).mp (show (⌈(v+U)/δ⌉₊:ℝ) < (v+U+δ)/δ by
        convert hlt using 1
        all_goals try with_reducible_and_instances rfl
        first | rfl | field_simp)
    dsimp [k]
    push_cast
    linarith

theorem Pencil.optimize_nearOptimal (B : Pencil n m) (f : Fin n → ℚ)
    (δ L R r U : ℚ) (z c : EuclideanSpace ℝ (Fin n))
    (hδ : 0 < δ) (hL : 0 < L) (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1)
    (hf : ‖objectiveCLM f‖ ≤ (L:ℝ)) (hzK : z ∈ B.feasible)
    (hz : ‖z‖ ≤ (R:ℝ)) (hc : ‖c‖ ≤ (R:ℝ))
    (hball : Metric.closedBall c (r:ℝ) ⊆ B.feasible)
    (hδsmall : δ ≤ L*(2*R+r))
    (hu : -(U:ℝ) ≤ objectiveCLM f z ∧ objectiveCLM f z ≤ (U:ℝ)) :
    let y := B.optimize f δ (nearRadius δ L R r) R U (optimizeFuel δ U)
    realVector y ∈ B.feasible ∧ objectiveCLM f (realVector y) ≤ objectiveCLM f z+2*(δ:ℝ) := by
  let a : ℝ := (δ:ℝ)/((L:ℝ)*(2*(R:ℝ)+(r:ℝ)))
  have hden : 0 < (L:ℝ)*(2*(R:ℝ)+(r:ℝ)) := by
    exact_mod_cast (show (0:ℚ) < L*(2*R+r) by positivity)
  have ha : 0 < a := div_pos (by exact_mod_cast hδ) hden
  have ha1 : a ≤ 1 := (div_le_one hden).mpr (by exact_mod_cast hδsmall)
  have hb := CurrentKS.RationalOptimization.nearOptimal_innerBall B.feasible B.convex_feasible
    (objectiveCLM f) z c (δ := (δ:ℝ)) hzK hf (by exact_mod_cast hL) (by exact_mod_cast hR)
    (by exact_mod_cast hr) hz hc hball (by exact_mod_cast hδ) (by exact_mod_cast hδsmall)
  obtain ⟨k,hk,hlo,hhi⟩ := exists_near_level (δ := (δ:ℝ)) (by exact_mod_cast hδ) hu.1 hu.2
  have hkr : k ≤ optimizeFuel δ U := by
    have hb : (2*(U:ℝ)/(δ:ℝ)) ≤ (⌈2*U/δ⌉₊:ℝ) := by
      exact_mod_cast (Nat.le_ceil (2*U/δ))
    exact hk.trans (Nat.add_le_add_right (Nat.ceil_le.mpr hb) 3)
  have he : (nearRadius δ L R r : ℝ)=a*(r:ℝ) := by
    simp only [nearRadius,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,a]
  have hcle : ‖(1-a) • z+a • c‖ ≤ (R:ℝ) := norm_convexCombination_le _ _ ha.le ha1 hz hc
  have haccept := B.levelCandidate_accepts f δ (nearRadius δ L R r) R U k
    ((1-a) • z+a • c) (nearRadius_pos hδ hL hR hr)
    ((nearRadius_le hL hR hr hδsmall).trans hr1) hR hcle (by
      rw [he]
      intro y hy
      have hy' := hb hy
      refine ⟨hy'.1,?_⟩
      change (fun i => (f i:ℝ)) ⬝ᵥ y ≤ (level δ U k:ℝ)
      rw [← objectiveCLM_apply]
      have hl : (level δ U k:ℝ)= -(U:ℝ)+(k:ℝ)*(δ:ℝ) := by simp [level]
      rw [hl]
      exact hy'.2.trans hlo)
  have hout := B.optimize_bound f δ (nearRadius δ L R r) R U hδ.le hkr haccept
  refine ⟨hout.1,?_⟩
  rw [objectiveCLM_apply]
  apply hout.2.trans
  simpa only [level,Rat.cast_add,Rat.cast_neg,Rat.cast_mul,Rat.cast_natCast] using hhi

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Point
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma feasible_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z.2.1 ∈ pd d ∧ z.2.2 ∈ pd d ∧
      invH z.2.1 + S + η z.2.2 ≤ z.1 • (Hermitian.one : H d) ∧
      invH z.2.2 - S + η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
  simp only [feasible, domain, residual, mem_ofPred_eq, sub_nonpos]
  tauto

lemma trace_bounds_of_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {z : Point d} (hz : z ∈ feasible S η) :
    0 ≤ z.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have htr₁ := realTrace_mono h₁
  have htr₂ := realTrace_mono h₂
  have hiX := realTrace_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY := realTrace_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX := realTrace_nonneg (hη _ hX.posSemidef)
  have heY := realTrace_nonneg (hη _ hY.posSemidef)
  simp only [realTrace_add, realTrace_sub, realTrace_smul, realTrace_one] at htr₁ htr₂
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  refine ⟨?_, realTrace_nonneg hX.posSemidef, realTrace_nonneg hY.posSemidef⟩
  nlinarith

lemma objective_bounds [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) {z : Point d} (hz : z ∈ feasible S η)
    (hf : objective ε z ≤ K) :
    0 ≤ z.1 ∧ z.1 ≤ K ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ≤ K / ε ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 ≤ K / ε := by
  obtain ⟨ht, hX, hY⟩ := trace_bounds_of_feasible S η hη hz
  simp only [objective, realTrace_add] at hf
  refine ⟨ht, ?_, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩ <;>
    nlinarith [mul_nonneg hε.le hX, mul_nonneg hε.le hY]

lemma inverse_bounds (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (ht : z.1 ≤ K) :
    invH z.2.1 ≤ (2*K) • (Hermitian.one : H d) ∧ invH z.2.2 ≤ (2*K) • (Hermitian.one : H d) := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have htk : z.1 • (Hermitian.one : H d) ≤ K • (Hermitian.one : H d) := scalar_one_mono ht
  constructor
  · have hh : invH z.2.1 + S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heY).trans (h₁.trans htk)
    have hx := add_le_add hh (neg_le_neg hS₁)
    convert hx using 1 <;> first | rfl | module
  · have hh : invH z.2.2 - S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heX).trans (h₂.trans htk)
    have hx := add_le_add hh hS₂
    convert hx using 1 <;> first | rfl | module

lemma sublevel_box [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (hf : objective ε z ≤ K) :
    z.1 ∈ Icc 0 K ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (K/ε) • (Hermitian.one : H d)) ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (K/ε) • (Hermitian.one : H d)) := by
  obtain ⟨ht, htK, htrX, htrY⟩ := objective_bounds S η hη hε hz hf
  obtain ⟨hXi, hYi⟩ := inverse_bounds S η hη hS₁ hS₂ hz htK
  obtain ⟨hX,hY,-,-⟩ := (feasible_iff S η z).mp hz
  have hmul : ∀ r s : ℝ, r ≤ s → r • (Hermitian.one : H d) ≤ s • (Hermitian.one : H d) :=
    fun _ _ h => scalar_one_mono h
  exact ⟨⟨ht,htK⟩,
    ⟨inverse_bound_below (by positivity) hX hXi,
      (trace_bound_above hX.posSemidef).trans (hmul _ _ htrX)⟩,
    ⟨inverse_bound_below (by positivity) hY hYi,
      (trace_bound_above hY.posSemidef).trans (hmul _ _ htrY)⟩⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_SchurBlock
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma schurBlock_psd_iff (T X : H d) (hX : X ∈ pd d) :
    (schurBlock T X).PosSemidef ↔ invH X ≤ T := by
  let : Invertible (X : Mat d) := hX.isUnit.invertible
  have hh := Matrix.PosDef.fromBlocks₂₂ (T : Mat d) (1 : Mat d) hX
  simp only [Matrix.conjTranspose_one,one_mul,mul_one] at hh
  change (schurBlock T X).PosSemidef ↔ ((T-invH X : H d) : Mat d).PosSemidef at hh
  rw [← mem_psdCone,mem_psd_iff_nonneg,sub_nonneg] at hh
  exact hh

lemma valueBlocks_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d)
    (hX : z.2.1 ∈ pd d) (hY : z.2.2 ∈ pd d) :
    (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef ↔ z ∈ feasible S η := by
  rw [valueBlock₁,valueBlock₂,schurBlock_psd_iff _ _ hX,schurBlock_psd_iff _ _ hY,feasible_iff]
  have h₁ : (invH z.2.1 ≤ z.1 • (Hermitian.one : H d)-S-η z.2.2) ↔
      invH z.2.1+S+η z.2.2 ≤ z.1 • (Hermitian.one : H d) := by
    rw [le_sub_iff_add_le,le_sub_iff_add_le]
    rw [show invH z.2.1+η z.2.2+S = invH z.2.1+S+η z.2.2 by module]
  have h₂ : (invH z.2.2 ≤ z.1 • (Hermitian.one : H d)+S-η z.2.1) ↔
      invH z.2.2-S+η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
    rw [le_sub_iff_add_le,← sub_le_iff_le_add]
    rw [show invH z.2.2+η z.2.1-S = invH z.2.2-S+η z.2.1 by module]
  rw [h₁,h₂]
  exact ⟨fun h => ⟨hX,hY,h.1,h.2⟩,fun h => ⟨h.2.2.1,h.2.2.2⟩⟩

lemma mem_valueSpectrahedron (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ valueSpectrahedron ε S η ↔ oracleBox ε z ∧ z ∈ feasible S η := by
  constructor
  · rintro ⟨hb,h₁,h₂⟩
    exact ⟨hb,(valueBlocks_iff S η z
      (pd_of_lower (by norm_num : (0:ℝ)<1/400) hb.2.1.1)
      (pd_of_lower (by norm_num : (0:ℝ)<1/400) hb.2.2.1)).mp ⟨h₁,h₂⟩⟩
  · rintro ⟨hb,hz⟩
    obtain ⟨hX,hY,_,_⟩ := (feasible_iff S η z).mp hz
    exact ⟨hb,(valueBlocks_iff S η z hX hY).mpr hz⟩

lemma sublevel_oracleBox [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hS₁ : -(100:ℝ) • (Hermitian.one : H d) ≤ S)
    (hS₂ : S ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible S η) (hf : objective ε z ≤ 100) : oracleBox ε z := by
  obtain ⟨ht,hX,hY⟩ := sublevel_box S η hη hε (show (0:ℝ)<100 by norm_num) hS₁ hS₂ hz hf
  have hl : (1/400 : ℝ) • (Hermitian.one : H d) ≤ (2*100:ℝ)⁻¹ • Hermitian.one :=
    scalar_one_mono (by norm_num)
  have hu : (100/ε : ℝ) • (Hermitian.one : H d) ≤ (200/ε) • Hermitian.one :=
    scalar_one_mono (div_le_div_of_nonneg_right (by norm_num) hε.le)
  exact ⟨ht,⟨hl.trans hX.1,hX.2.trans hu⟩,⟨hl.trans hY.1,hY.2.trans hu⟩⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_PackValue
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma time_packValue (z : Point d) : timeCoordinate d (packValue z) = z.1 := by
  simp [timeCoordinate,packValue]
lemma matrix_packValue (z : Point d) (second : Bool) :
    matrixCoordinate d second (packValue z) = encode (if second then z.2.2 else z.2.1) := by
  funext ij
  cases second <;> simp [matrixCoordinate,packValue]
lemma unpack_packValue (z : Point d) : unpackValue (packValue z)=z := by
  simp only [unpackValue,time_packValue,matrix_packValue,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  change (z.1,assemble (extract z.2.1),assemble (extract z.2.2))=z
  rw [assemble_extract,assemble_extract]

lemma complexValueProgram_iff (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (ηm : Mat d → Mat d) (hηm : ∀ W : H d,ηm W=(η W : Mat d)) (z : Point d) :
    complexValueProgram ε S ηm z.1 z.2.1 z.2.2 ↔ z ∈ valueSpectrahedron ε S η := by
  have ho (A B : H d) : ((B : Mat d)-A).PosSemidef ↔ A ≤ B := by
    change ((B-A : H d) : Mat d).PosSemidef ↔ _
    rw [← mem_psdCone,mem_psd_iff_nonneg,sub_nonneg]
  simp only [complexValueProgram,hηm]
  change (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef ∧
    ((z.2.1 : Mat d)-((1/400:ℝ) • Hermitian.one : H d)).PosSemidef ∧
    (((200/ε:ℝ) • Hermitian.one : H d)- (z.2.1 : Mat d)).PosSemidef ∧
    ((z.2.2 : Mat d)-((1/400:ℝ) • Hermitian.one : H d)).PosSemidef ∧
    (((200/ε:ℝ) • Hermitian.one : H d)- (z.2.2 : Mat d)).PosSemidef ∧
    0 ≤ z.1 ∧ z.1 ≤ 100 ↔ _
  rw [ho,ho,ho,ho]
  simp only [valueSpectrahedron,Set.mem_ofPred_eq,oracleBox,Set.mem_Icc]
  tauto

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueOuterRadius
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d n : ℕ}

lemma euclidean_norm_le_card (v : EuclideanSpace ℝ (Fin n)) {B : ℝ}
    (hB : 0 ≤ B) (hv : ∀ k, ‖v k‖ ≤ B) : ‖v‖ ≤ ((n:ℝ)+1)*B := by
  have hs : ‖v‖^2 ≤ (n:ℝ)*B^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
      sq_le_sq₀ (norm_nonneg _) hB |>.mpr (hv k))
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hnum : (n:ℝ) ≤ ((n:ℝ)+1)^2 := by have := Nat.cast_nonneg (α := ℝ) n; nlinarith
  have hm := mul_le_mul_of_nonneg_right hnum (sq_nonneg B)
  have hp : 0 ≤ ((n:ℝ)+1)*B := by positivity
  nlinarith [norm_nonneg v]

lemma norm_hermitian_entry (A : H d) (i j : Fin d) : ‖A.val i j‖ ≤ ‖A‖ := by
  change ‖asL2 A.val i j‖ ≤ ‖asL2 A.val‖
  exact (PiLp.norm_apply_le (asL2 A.val i) j).trans (PiLp.norm_apply_le (asL2 A.val) i)

lemma abs_encode_le (A : H d) (ij : Fin d × Fin d) : |encode A ij| ≤ ‖A‖ := by
  unfold encode
  split
  · exact (Complex.abs_re_le_norm _).trans (norm_hermitian_entry A _ _)
  · exact (Complex.abs_im_le_norm _).trans (norm_hermitian_entry A _ _)

lemma norm_packValue (z : Point d) :
    ‖packValue z‖ ≤ ((valueDimension d:ℝ)+1)*(|z.1|+‖z.2.1‖+‖z.2.2‖) := by
  apply euclidean_norm_le_card _ (by positivity)
  intro k
  obtain ⟨j,rfl⟩ := (valueIndex d).surjective k
  rcases j with j | (ij | ij)
  · simp only [packValue,PiLp.toLp_apply,Equiv.symm_apply_apply,Real.norm_eq_abs]
    linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
  · simp only [packValue,PiLp.toLp_apply,Equiv.symm_apply_apply,Real.norm_eq_abs]
    have he := abs_encode_le z.2.1 ij
    linarith [abs_nonneg z.1,norm_nonneg z.2.2]
  · simp only [packValue,PiLp.toLp_apply,Equiv.symm_apply_apply,Real.norm_eq_abs]
    have he := abs_encode_le z.2.2 ij
    linarith [abs_nonneg z.1,norm_nonneg z.2.1]

lemma norm_psd_order_bound (U : H d) (hU : U ∈ psdCone d) {r : ℝ} (hr : 0 ≤ r)
    (hUr : U ≤ r • Hermitian.one) : ‖U‖ ≤ r*((d:ℝ)+1) := by
  have ht := realTrace_mono hUr
  rw [Hermitian.realTrace_smul,Hermitian.realTrace_one] at ht
  have hh := inner_nonneg_of_psd U (r • Hermitian.one-U) hU
    ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUr))
  rw [inner_sub_right,real_inner_smul_right U (Hermitian.one : H d) r,inner_one',real_inner_self_eq_norm_sq] at hh
  have hnt : ‖U‖^2 ≤ r^2*d := by nlinarith [mul_le_mul_of_nonneg_left ht hr]
  have hd : (0:ℝ)≤d := Nat.cast_nonneg d
  have hd' : (d:ℝ)≤(d+1)^2 := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hd' (sq_nonneg r)
  have hn : 0 ≤ r*((d:ℝ)+1) := by positivity
  nlinarith [norm_nonneg U]

lemma valueOuterRadius_nonneg {ε : ℚ} (hε : 0 < ε) : 0 ≤ valueOuterRadius d ε := by
  unfold valueOuterRadius
  positivity
lemma valueInnerRadius_pos : 0 < valueInnerRadius d := by unfold valueInnerRadius; positivity
lemma valueInnerRadius_le : valueInnerRadius d ≤ 1 := by
  unfold valueInnerRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg (d:ℚ)]

lemma oracleBox_norm_packValue {ε : ℚ} (hε : 0 < ε) (z : Point d) (hz : oracleBox (ε:ℝ) z) :
    ‖packValue z‖ ≤ (valueOuterRadius d ε:ℝ) := by
  have hX := (pd_of_lower (by norm_num : (0:ℝ)<1/400) hz.2.1.1).posSemidef
  have hY := (pd_of_lower (by norm_num : (0:ℝ)<1/400) hz.2.2.1).posSemidef
  have hεr : (0:ℝ)<ε := by exact_mod_cast hε
  have hx := norm_psd_order_bound z.2.1 hX (div_nonneg (by norm_num) hεr.le) hz.2.1.2
  have hy := norm_psd_order_bound z.2.2 hY (div_nonneg (by norm_num) hεr.le) hz.2.2.2
  have ht : |z.1| ≤ 100 := by rw [abs_of_nonneg hz.1.1]; exact hz.1.2
  apply (norm_packValue z).trans
  unfold valueOuterRadius
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ 100+(200/(ε:ℝ)*((d:ℝ)+1)+200/(ε:ℝ)*((d:ℝ)+1)) := by linarith
    _ = _ := by ring

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ValueObjectiveCoeffs
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma valueObjectiveCoeffs_real (ε : ℚ) (v : Fin (valueDimension d) → ℝ) :
    (fun i => (valueObjectiveCoeffs d ε i:ℝ)) ⬝ᵥ v =
      timeCoordinate d v+(ε:ℝ)*∑ i : Fin d,
        (matrixCoordinate d false v (i,i)+matrixCoordinate d true v (i,i)) := by
  have he : (fun i => (valueObjectiveCoeffs d ε i:ℝ)) =
      Pi.single (valueIndex d (.inl 0)) 1 + (ε:ℝ) •
      ∑ i : Fin d,(Pi.single (valueIndex d (.inr (.inl (i,i)))) 1+
        Pi.single (valueIndex d (.inr (.inr (i,i)))) 1) := by
    have hs (j k : Fin (valueDimension d)) :
        ((Pi.single j (1:ℚ) : Fin (valueDimension d) → ℚ) k : ℝ) =
          (Pi.single j (1:ℝ) : Fin (valueDimension d) → ℝ) k := by
      by_cases h : j=k
      · subst k; simp
      · simp [h]
    ext k
    simp only [valueObjectiveCoeffs,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,
      smul_eq_mul,Rat.cast_add,Rat.cast_mul,Rat.cast_sum,hs]
  rw [he]
  simp [add_dotProduct,smul_dotProduct,sum_dotProduct,
    single_dotProduct,timeCoordinate,matrixCoordinate,smul_eq_mul]

lemma objectiveCLM_value (ε : ℚ) (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    objectiveCLM (valueObjectiveCoeffs d ε) v = objective (ε:ℝ) (unpackValue v) := by
  rw [objectiveCLM_apply,valueObjectiveCoeffs_real]
  simp only [objective,unpackValue,realTrace_add]
  congr 1
  simp only [assemble,Hermitian.realTrace,trace_decode,← Finset.sum_add_distrib]

lemma valueObjectiveCoeffs_bound {ε : ℚ} (hε : 0 ≤ ε) (k : Fin (valueDimension d)) :
    |valueObjectiveCoeffs d ε k| ≤ 1+2*ε*d := by
  have hp (j : Fin (valueDimension d)) :
      0 ≤ (Pi.single j (1:ℚ) : Fin (valueDimension d) → ℚ) k ∧
      (Pi.single j (1:ℚ) : Fin (valueDimension d) → ℚ) k ≤ 1 := by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hs : (∑ i : Fin d,
      ((Pi.single (valueIndex d (.inr (.inl (i,i)))) (1:ℚ) : Fin (valueDimension d) → ℚ) k+
      (Pi.single (valueIndex d (.inr (.inr (i,i)))) (1:ℚ) : Fin (valueDimension d) → ℚ) k)) ≤ 2*d := by
    calc
      _ ≤ ∑ _ : Fin d,(2:ℚ) := Finset.sum_le_sum fun i _ => by
        have h₁ := (hp (valueIndex d (.inr (.inl (i,i))))).2
        have h₂ := (hp (valueIndex d (.inr (.inr (i,i))))).2
        linarith
      _ = _ := by simp <;> ring
  have hn : 0 ≤ valueObjectiveCoeffs d ε k := by
    simp only [valueObjectiveCoeffs,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
    exact add_nonneg (hp _).1 (mul_nonneg hε (Finset.sum_nonneg fun i _ =>
      add_nonneg (hp _).1 (hp _).1))
  rw [abs_of_nonneg hn]
  simp only [valueObjectiveCoeffs,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  have ht := (hp (valueIndex d (.inl 0))).2
  have hm := mul_le_mul_of_nonneg_left hs hε
  nlinarith

lemma valueLipschitz_pos {ε : ℚ} (hε : 0 ≤ ε) : 0 < valueLipschitz d ε := by
  unfold valueLipschitz
  positivity

lemma objectiveCLM_value_norm {ε : ℚ} (hε : 0 ≤ ε) :
    ‖objectiveCLM (valueObjectiveCoeffs d ε)‖ ≤ (valueLipschitz d ε:ℝ) := by
  have hb : ‖realVector (valueObjectiveCoeffs d ε)‖ ≤
      ((valueDimension d:ℝ)+1)*(1+2*(ε:ℝ)*d) := by
    apply euclidean_norm_le_card _ (by exact_mod_cast (show (0:ℚ)≤1+2*ε*d by positivity))
    intro k
    change ‖(valueObjectiveCoeffs d ε k:ℝ)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact_mod_cast valueObjectiveCoeffs_bound hε k
  change ‖innerSL ℝ (realVector (valueObjectiveCoeffs d ε))‖ ≤ _
  rw [innerSL_apply_norm]
  simpa only [valueLipschitz,Rat.cast_mul,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast] using hb

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_reaa21f_2 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma sum_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) : (∑ i, A i) ≤ (Hermitian.one : H d) := by
  have hp := trace_bound_above (psd_sum Finset.univ A fun i _ => hA i)
  simpa only [realTrace_sum,htr,one_smul] using hp

lemma S_bounds (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) {x : Coordinates N} (hx : Cube x) :
    -(Hermitian.one : H d) ≤ S A x ∧ S A x ≤ (Hermitian.one : H d) := by
  have hsum := sum_le_one A hA htr
  have hupper : S A x ≤ ∑ i, A i := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_smul] using scalar_mono_psd (hA i) (abs_le.mp (hx i)).2
  have hlower : -(∑ i, A i) ≤ S A x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := scalar_mono_psd (hA i) (abs_le.mp (hx i)).1
    have he : (-1 : ℝ) • A i = -A i := neg_one_smul ℝ (A i)
    rw [he] at hh
    exact hh
  exact ⟨(neg_le_neg hsum).trans hlower,hupper.trans hsum⟩

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Value
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma value_eq_of_min (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    value ε S η = objective ε z := by
  apply IsLeast.csInf_eq
  refine ⟨⟨z,hz,rfl⟩,?_⟩
  rintro b ⟨w,hw,rfl⟩
  exact hmin w hw

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueFeasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p8
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedSpace
lemma value_le_feasible [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    value ε S η ≤ objective ε z := by
  have hb : BddBelow (objective ε '' feasible S η) := by
    refine ⟨0,?_⟩
    rintro r ⟨w,hw,rfl⟩
    obtain ⟨ht,hX,hY⟩ := trace_bounds_of_feasible S η hη hw
    simp only [objective,realTrace_add]
    exact add_nonneg ht (mul_nonneg hε (add_nonneg hX hY))
  exact csInf_le hb ⟨z,hz,rfl⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ParameterCube
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma etaTheta_apply (c : ℝ) (A : Fin N → H d) (θ : Coordinates N) (Z : H d) :
    etaTheta c A θ Z = ∑ i,(c*θ i) • sandwich (A i) Z := by
  exact sum_apply Finset.univ (fun i => (c*θ i) • sandwichCLM (A i)) Z

lemma etaTheta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {θ : Coordinates N}
    (hθ : ParameterCube θ) : ∀ Z ∈ psdCone d, etaTheta c A θ Z ∈ psdCone d := by
  intro Z hZ
  rw [etaTheta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (hθ i).1)

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RationalAtoms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma complexSum_rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (x : Fin N → ℚ) :
    complexSum (fun i j => (coords i j:ℝ)) (fun i => (x i:ℝ)) =
      ((S (rationalAtoms coords) (fun i => (x i:ℝ))) : Mat d) := by
  simp only [complexSum,S,Submodule.coe_sum,Submodule.coe_smul_of_tower,
    rationalAtoms,assemble]

lemma complexEta_rationalAtoms (coords : Fin N → Fin d × Fin d → ℚ) (θ : Fin N → ℚ)
    (Z : H d) :
    complexEta (fun i j => (coords i j:ℝ)) (fun i => (θ i:ℝ)) Z =
      ((etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ))) Z : Mat d) := by
  rw [etaTheta_apply]
  simp only [complexEta,Submodule.coe_sum,Submodule.coe_smul_of_tower,rationalAtoms,assemble]
  rfl

lemma valuePencil_feasible (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (ε : ℚ) (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    v ∈ (valuePencil coords x θ ε).feasible ↔
      unpackValue v ∈ valueSpectrahedron (ε:ℝ)
        (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ))) := by
  change ((valuePencil coords x θ ε).realEval v).PosSemidef ↔ _
  rw [valuePencil_psd,complexSum_rationalAtoms]
  exact complexValueProgram_iff _ _ _ _ (complexEta_rationalAtoms coords θ) (unpackValue v)

lemma valueOuterRadius_le {ε : ℚ} (hε : 0 < ε) : 100 ≤ valueOuterRadius d ε := by
  have hm : (0:ℚ) ≤ 400/ε*((d:ℚ)+1) := by positivity
  have hd : (0:ℚ) ≤ valueDimension d := Nat.cast_nonneg _
  unfold valueOuterRadius
  nlinarith

lemma valueLipschitz_le {ε : ℚ} (hε : 0 ≤ ε) : 1 ≤ valueLipschitz d ε := by
  have hm : (0:ℚ) ≤ 2*ε*d := by positivity
  have hd : (0:ℚ) ≤ valueDimension d := Nat.cast_nonneg _
  unfold valueLipschitz
  nlinarith


lemma valueQueryPoint_correct_oai [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν δ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ))) :
    let ε : ℚ := ν/d
    let y := valueQueryPoint coords x θ ν δ
    realVector y ∈ (valuePencil coords x θ ε).feasible ∧
      |(valueQuery coords x θ ν δ:ℝ)-value (ε:ℝ)
        (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ)))| ≤ 2*(δ:ℝ) := by
  let ε : ℚ := ν/d
  let A := rationalAtoms coords
  let xr : Coordinates N := fun i => (x i:ℝ)
  let θr : Coordinates N := fun i => (θ i:ℝ)
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ε := div_pos hν hd
  have hε1 : ε ≤ 1 := (div_le_one hd).mpr (hν1.trans hd1)
  have hεr : (ε:ℝ) = (ν:ℝ)/d := by simp [ε]
  have hpos := etaTheta_positive (show (0:ℝ)≤384 by norm_num) A hθ
  obtain ⟨z,hz,hz100,hzmin⟩ := etaTheta_minimizer A hA htr (by exact_mod_cast hν)
    (by exact_mod_cast hν1) hvar xr θr hx hθ
  rw [← hεr] at hz100 hzmin
  have hSl : -(100:ℝ) • (Hermitian.one : H d) ≤ S A xr := by
    have hb := (S_bounds A hA htr hx).1
    exact (show -(100:ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      calc
        (-100:ℝ) • (Hermitian.one : H d) ≤ (-1:ℝ) • Hermitian.one :=
          scalar_one_mono (by norm_num)
        _ = -Hermitian.one := neg_one_smul ℝ (Hermitian.one : H d)).trans hb
  have hSu : S A xr ≤ (100:ℝ) • (Hermitian.one : H d) := by
    exact (S_bounds A hA htr hx).2.trans (by
      simpa only [one_smul] using scalar_one_mono (d := d) (show (1:ℝ)≤100 by norm_num))
  have hbz := sublevel_oracleBox (S A xr) (etaTheta 384 A θr) hpos
    (by exact_mod_cast hε) hSl hSu z hz hz100
  have hzK : packValue z ∈ (valuePencil coords x θ ε).feasible := by
    rw [valuePencil_feasible,unpack_packValue]
    exact (mem_valueSpectrahedron _ _ _ _).mpr ⟨hbz,hz⟩
  let c : Point d := (50,(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • Hermitian.one)
  have hball := valuePencil_ball coords x θ hA htr (by exact_mod_cast hν1) hvar hx hθ hε hε1
  have hcK : packValue c ∈ (valuePencil coords x θ ε).feasible :=
    hball (by exact Metric.mem_closedBall_self (by exact_mod_cast (valueInnerRadius_pos (d := d)).le))
  have hbc : oracleBox (ε:ℝ) c := by
    have hh := (valuePencil_feasible coords x θ ε (packValue c)).mp hcK
    rw [unpack_packValue] at hh
    exact (mem_valueSpectrahedron _ _ _ _).mp hh |>.1
  have hsmall : δ ≤ valueLipschitz d ε*(2*valueOuterRadius d ε+valueInnerRadius d) := by
    have hl := valueLipschitz_le (d := d) hε.le
    have hr := valueOuterRadius_le (d := d) hε
    have hi := valueInnerRadius_pos (d := d)
    nlinarith
  have hzn : 0 ≤ objective (ε:ℝ) z := by
    obtain ⟨hzt,hzX,hzY⟩ := trace_bounds_of_feasible (S A xr) (etaTheta 384 A θr) hpos hz
    simp only [objective,Hermitian.realTrace_add]
    exact add_nonneg hzt (mul_nonneg (by exact_mod_cast hε.le) (add_nonneg hzX hzY))
  have hres := (valuePencil coords x θ ε).optimize_nearOptimal (valueObjectiveCoeffs d ε)
    δ (valueLipschitz d ε) (valueOuterRadius d ε) (valueInnerRadius d) 100 (packValue z) (packValue c)
    hδ (valueLipschitz_pos hε.le) (valueOuterRadius_nonneg hε) valueInnerRadius_pos valueInnerRadius_le
    (objectiveCLM_value_norm hε.le) hzK (oracleBox_norm_packValue hε z hbz)
    (oracleBox_norm_packValue hε c hbc) hball hsmall (by
      rw [objectiveCLM_value,unpack_packValue]
      exact ⟨by norm_num <;> linarith,hz100⟩)
  change realVector (valueQueryPoint coords x θ ν δ) ∈ (valuePencil coords x θ ε).feasible ∧
    objectiveCLM (valueObjectiveCoeffs d ε) (realVector (valueQueryPoint coords x θ ν δ)) ≤
      objectiveCLM (valueObjectiveCoeffs d ε) (packValue z)+2*(δ:ℝ) at hres
  have he : (valueQuery coords x θ ν δ:ℝ) =
      objectiveCLM (valueObjectiveCoeffs d ε) (realVector (valueQueryPoint coords x θ ν δ)) := by
    rw [objectiveCLM_apply]
    unfold valueQuery
    rw [← valueObjectiveCoeffs_dot]
    simp only [dotProduct,Rat.cast_sum,Rat.cast_mul,realVector,PiLp.toLp_apply]
    rfl
  have hmin := value_eq_of_min (ε:ℝ) (S A xr) (etaTheta 384 A θr) z hz hzmin
  have hyv := (mem_valueSpectrahedron _ _ _ _).mp
    ((valuePencil_feasible coords x θ ε _).mp hres.1) |>.2
  have hlow := value_le_feasible (ε:ℝ) (by exact_mod_cast hε.le) (S A xr)
    (etaTheta 384 A θr) hpos _ hyv
  refine ⟨hres.1,?_⟩
  change |(valueQuery coords x θ ν δ:ℝ)-value (ε:ℝ) (S A xr) (etaTheta 384 A θr)| ≤ _
  have hu := hres.2
  rw [objectiveCLM_value,objectiveCLM_value,unpack_packValue,← hmin] at hu
  rw [he,objectiveCLM_value,abs_of_nonneg (sub_nonneg.mpr hlow)]
  linarith

end CurrentKS.RationalSDP

end

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.RationalSDP.valueQueryPoint_correct_oai := @OAI.CurrentKS.RationalSDP.valueQueryPoint_correct_oai
