-- Prove2me | solution 1 for OAI.CurrentKS.RationalFace.transition_spec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:35.824439+00:00
-- url     : https://prove2.me/submissions/09f4d39b-94c3-4374-aa26-9860880d3ec2

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_RationalFace_faceCandidates_progress
import Theorems.Thm_OAI_CurrentKS_RationalSDP_valueQueryPoint_correct
import Theorems.Thm_OAI_CurrentKS_State_etaTheta_minimizer

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_CubeInterval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar

lemma cubeInterval_spec (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) :
    0 ≤ (cubeInterval q k).1 ∧ (cubeInterval q k).2 ≤ 1 ∧
    ((cubeInterval q k).1:ℝ) ≤ r ∧ r ≤ ((cubeInterval q k).2:ℝ) ∧
    (cubeInterval q k).2-(cubeInterval q k).1=(1/2:ℚ)^k := by
  induction k with
  | zero => simpa [cubeInterval] using And.intro hr hr1
  | succ k ih =>
    have horder : (cubeInterval q k).1 ≤ (cubeInterval q k).2 := by
      exact_mod_cast ih.2.2.1.trans ih.2.2.2.1
    let m : ℚ := ((cubeInterval q k).1+(cubeInterval q k).2)/2
    have hml : (cubeInterval q k).1 ≤ m := by dsimp [m] <;> linarith
    have hmu : m ≤ (cubeInterval q k).2 := by dsimp [m] <;> linarith
    have hm : 0 ≤ m := ih.1.trans hml
    have hmr : (0:ℝ) ≤ m := by exact_mod_cast hm
    have he : cubeInterval q (k+1) = if m^3 ≤ q then (m,(cubeInterval q k).2) else ((cubeInterval q k).1,m) := rfl
    rw [he]
    split
    · rename_i h
      have hc : (m:ℝ)^3 ≤ r^3 := by rw [← hq]; exact_mod_cast h
      have hle := (pow_le_pow_iff_left₀ hmr hr (by decide : 3≠0)).mp hc
      refine ⟨hm,ih.2.1,hle,ih.2.2.2.1,?_⟩
      change (cubeInterval q k).2-m=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring
    · rename_i h
      have hc : r^3 ≤ (m:ℝ)^3 := by rw [← hq]; exact_mod_cast (le_of_lt (lt_of_not_ge h))
      have hle := (pow_le_pow_iff_left₀ hr hmr (by decide : 3≠0)).mp hc
      refine ⟨ih.1,hmu.trans ih.2.1,ih.2.2.1,hle,?_⟩
      change m-(cubeInterval q k).1=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring

lemma cubeInterval_error (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) :
    |((cubeInterval q k).1:ℝ)-r| ≤ (1/2:ℝ)^k := by
  obtain ⟨_,_,hl,hu,hw⟩ := cubeInterval_spec q r hr hr1 hq k
  have hwr : ((cubeInterval q k).2:ℝ)-(cubeInterval q k).1=(1/2:ℝ)^k := by
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hw
    norm_num only [Rat.cast_sub,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hc
    exact hc
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

lemma cubeInterval_lower_mem (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) : (cubeInterval q k).1 ∈ Set.Icc (0:ℚ) 1 := by
  have h := cubeInterval_spec q r hr hr1 hq k
  exact ⟨h.1,by exact_mod_cast h.2.2.1.trans hr1⟩

lemma psi_closed_cube {x : ℝ} (hx : |x| ≤ 1) : psi x^3=1-x^2 := by
  have hb : 0 ≤ 1-x^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hx
    nlinarith
  rw [psi,← Real.rpow_natCast,← Real.rpow_mul hb]
  norm_num
lemma psi_closed_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hc := psi_closed_cube hx
  have hb : 0 ≤ 1-x^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hx
    nlinarith
  have hp : 0 ≤ psi x := Real.rpow_nonneg hb _
  refine ⟨hp,(pow_le_pow_iff_left₀ hp (by norm_num : (0:ℝ) ≤ 1) (by decide : 3≠0)).mp ?_⟩
  rw [hc]
  nlinarith [sq_nonneg x]

lemma inverse_pow_size_le {δ : ℚ} (hδ : 0 < δ) : (1/2:ℚ)^δ.den.size ≤ δ := by
  have hd : (0:ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hp : (0:ℚ) < 2^δ.den.size := by positivity
  have hnum : (1:ℚ) ≤ δ.num := by exact_mod_cast (Int.add_one_le_iff.mpr (Rat.num_pos.mpr hδ))
  have hden : (δ.den:ℚ) ≤ 2^δ.den.size := by exact_mod_cast (Nat.lt_size_self δ.den).le
  rw [_root_.one_div_pow,one_div]
  calc
    (2^δ.den.size:ℚ)⁻¹ ≤ (δ.den:ℚ)⁻¹ := inv_anti₀ hd hden
    _ ≤ (δ.num:ℚ)/(δ.den:ℚ) := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hnum hd.le
    _ = δ := Rat.num_div_den δ

lemma approxPsi_spec (x δ : ℚ) (hx : |(x:ℝ)| ≤ 1) (hδ : 0 < δ) :
    approxPsi x δ ∈ Set.Icc (0:ℚ) 1 ∧ |(approxPsi x δ:ℝ)-psi (x:ℝ)| ≤ (δ:ℝ) := by
  obtain ⟨hp,hp1⟩ := psi_closed_bounds hx
  have hc : ((1-x^2:ℚ):ℝ)=psi (x:ℝ)^3 := by rw [psi_closed_cube hx]; push_cast; rfl
  refine ⟨cubeInterval_lower_mem _ _ hp hp1 hc _,?_⟩
  have he : (((1/2:ℚ)^δ.den.size : ℚ):ℝ) ≤ (δ:ℝ) := Rat.cast_le.mpr (inverse_pow_size_le hδ)
  norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at he
  exact (cubeInterval_error _ _ hp hp1 hc _).trans he

end CurrentKS.Scalar

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

theorem rankOne_mem_psdCone (v : Fin d → ℂ) : rankOne v ∈ psdCone d :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem inner_rankOne (A : H d) (v : Fin d → ℂ) :
    inner ℝ A (rankOne v) = (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re := by
  rw [inner_eq_trace]
  change ((A : Mat d) * Matrix.vecMulVec v (star v)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem psd_of_inner_nonneg (A : H d)
    (h : ∀ B ∈ psdCone d, 0 ≤ inner ℝ A B) : A ∈ psdCone d := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.property, fun v => ?_⟩
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [inner_rankOne] using h (rankOne v) (rankOne_mem_psdCone v)
  · exact (A.property.im_star_dotProduct_mulVec_self v).symm

theorem isClosed_psdCone : IsClosed (psdCone d : Set (H d)) := by
  have he : (psdCone d : Set (H d)) =
      {A : H d | ∀ v : Fin d → ℂ, 0 ≤ (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re} := by
    ext A
    constructor
    · intro hA v
      exact hA.re_dotProduct_nonneg v
    · intro hA
      apply psd_of_inner_nonneg A

      have hp : (A : Mat d).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨A.property, fun v =>
          Complex.nonneg_iff.mpr ⟨hA v, (A.property.im_star_dotProduct_mulVec_self v).symm⟩⟩
      exact fun B hB => inner_nonneg_of_psd A B hp hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (continuous_subtype_val.matrix_mulVec continuous_const))

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

lemma pd_smul {A : H d} (hA : A ∈ pd d) {a : ℝ} (ha : 0 < a) :
    a • A ∈ pd d := by
  change ((a : ℂ) • (A : Mat d)).PosDef
  exact hA.smul (by exact_mod_cast ha)

lemma isClosed_lowerBound (a : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A} := by
  change IsClosed ((fun A : H d => A - a • one) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_id.sub continuous_const)

lemma isClosed_upperBound (b : ℝ) :
    IsClosed {A : H d | A ≤ (b • one : H d)} := by
  change IsClosed ((fun A : H d => b • one - A) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_const.sub continuous_id)

lemma isClosed_orderBox (a b : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} :=
  (isClosed_lowerBound a).inter (isClosed_upperBound b)

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

theorem isCompact_orderBox (a b : ℝ) :
    IsCompact {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} := by
  let : CStarAlgebra (Mat d) := {}
  let : ProperSpace (H d) := FiniteDimensional.proper ℝ (H d)
  apply (isCompact_closedBall (a • one : H d) ‖(b-a) • (one : H d)‖).of_isClosed_subset
    (isClosed_orderBox a b)
  intro A hA
  rw [Metric.mem_closedBall]
  change dist (A : Mat d) (a • (1 : Mat d)) ≤ ‖(b-a) • (1 : Mat d)‖
  rw [dist_eq_norm]
  have h₁ : a • (1 : Mat d) ≤ (A : Mat d) := hA.1
  have h₂ : (A : Mat d) ≤ b • (1 : Mat d) := hA.2
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg _ (sub_nonneg.mpr h₁)
  have hh := sub_le_sub_right h₂ (a • (1 : Mat d))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Complex.ofReal_sub]
  ring

end
end CurrentKS.Hermitian

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

lemma operatorNorm_nonneg (A : H d) : 0 ≤ operatorNorm A := norm_nonneg _

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

lemma operatorNorm_smul (r : ℝ) (A : H d) : operatorNorm (r • A) = |r| * operatorNorm A := by
  change ‖(r : ℂ) • (A : Mat d)‖ = _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  rfl

end

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

end CurrentKS.Hermitian

end

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

lemma continuous_realTrace : Continuous (realTrace : H d → ℝ) := by
  have he : (fun A : H d => traceCLM A) = realTrace := funext traceCLM_apply
  rw [← he]
  exact (traceCLM (d := d)).continuous

lemma continuousAt_invH {A : H d} (hA : A ∈ pd d) : ContinuousAt invH A := by
  have hm : ContinuousAt (Inv.inv : Mat d → Mat d) (A : Mat d) := by
    apply continuousAt_matrix_inv
    have he : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [he]
    exact continuousAt_inv₀ hA.det_pos.ne'
  apply tendsto_subtype_rng.mpr
  exact hm.comp continuousAt_subtype_val

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_OperatorNormSquare
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
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

variable {d N : ℕ}

lemma operatorNorm_square (A : H d) :
    operatorNorm (sandwich A (one : H d))=(operatorNorm A)^2 := by
  let : CStarAlgebra (Mat d) := {}
  have he := A.property.isSelfAdjoint.norm_mul_self
  simpa only [operatorNorm_eq_matrix,sandwich_val,one_val,mul_one] using he

lemma atom_operatorNorm_le_sqrt (A : Fin N → H d) {ν : ℝ} (hν : 0≤ν)
    (hvar : (∑ i,sandwich (A i) (one : H d))≤ν • (one : H d)) (i : Fin N) :
    operatorNorm (A i)≤Real.sqrt ν := by
  have hle : sandwich (A i) (one : H d)≤ν • (one : H d) :=
    (Finset.single_le_sum (fun j _ => psd_nonneg (sandwich_psd (A j) _ one_mem_psdCone))
      (Finset.mem_univ i)).trans hvar
  have hn := operatorNorm_le_of_psd_le (sandwich_psd (A i) _ one_mem_psdCone) hν hle
  rw [operatorNorm_square] at hn
  exact (Real.le_sqrt (operatorNorm_nonneg _) hν).mpr hn

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

lemma smul_order {A B : H d} (h : A ≤ B) {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply sub_nonneg.mp
  rw [← smul_sub r B A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)) hr)

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

lemma invH_scalar (a : ℝ) : invH (a • (Hermitian.one : H d)) = a⁻¹ • (Hermitian.one : H d) := by
  apply Subtype.ext
  change (a • (1 : Mat d))⁻¹ = a⁻¹ • (1 : Mat d)
  have h (r : ℝ) : r • (1 : Mat d) = (r : ℂ) • (1 : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [h a, h a⁻¹, Complex.ofReal_inv]
  exact scalar_inv a

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
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

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p7
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rd39747_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7
lemma sandwich_sub (A U V : H d) : sandwich A (U-V) = sandwich A U - sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)-(V : Mat d)) * (A : Mat d) = _
  simp only [mul_sub, sub_mul]
  rfl

end
end CurrentKS.Hermitian

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

lemma continuous_objective (ε : ℝ) : Continuous (objective (d := d) ε) := by
  exact continuous_fst.add (continuous_const.mul
    (continuous_realTrace.comp ((continuous_fst.comp continuous_snd).add
      (continuous_snd.comp continuous_snd))))

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairCone
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

lemma isClosed_pairCone : IsClosed (pairCone d : Set (H d × H d)) :=
  (isClosed_psdCone (d := d)).prod (isClosed_psdCone (d := d))

lemma feasible_iff_cone (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z ∈ domain d ∧ -residual S η z ∈ pairCone d := by
  simp only [feasible, mem_ofPred_eq, mem_pairCone, Prod.fst_neg, Prod.snd_neg]
  simp only [mem_psd_iff_nonneg, neg_nonneg]

lemma continuousOn_residual (S : H d) (η : H d →L[ℝ] H d) :
    ContinuousOn (residual S η) (domain d) := by
  intro z hz
  have hiX : ContinuousAt (fun z : Point d => invH z.2.1) z :=
    (continuousAt_invH hz.1).comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have hiY : ContinuousAt (fun z : Point d => invH z.2.2) z :=
    (continuousAt_invH hz.2).comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  have heX : ContinuousAt (fun z : Point d => η z.2.1) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have heY : ContinuousAt (fun z : Point d => η z.2.2) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  exact (((hiX.add continuousAt_const).add heY).sub
    (continuousAt_fst.smul continuousAt_const)).prodMk
      (((hiY.sub continuousAt_const).add heX).sub
        (continuousAt_fst.smul continuousAt_const)) |>.continuousWithinAt

theorem exists_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z₀ : Point d) (hz₀ : z₀ ∈ feasible S η) (hf₀ : objective ε z₀ ≤ K) :
    ∃ z ∈ feasible S η, objective ε z ≤ K ∧
      ∀ w ∈ feasible S η, objective ε z ≤ objective ε w := by
  let B : Set (Point d) := Icc 0 K ×ˢ
    ({A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)} ×ˢ
      {A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)})
  have hBc : IsCompact B := isCompact_Icc.prod
    ((isCompact_orderBox _ _).prod (isCompact_orderBox _ _))
  have hBD : B ⊆ domain d := by
    intro z hz
    exact ⟨pd_of_lower (by positivity) hz.2.1.1, pd_of_lower (by positivity) hz.2.2.1⟩
  let F : Point d → (H d × H d) × ℝ := fun z => (-residual S η z, objective ε z)
  have hFc : ContinuousOn F B := ((continuousOn_residual S η).mono hBD).neg.prodMk
    (continuous_objective ε).continuousOn
  let C : Set (Point d) := B ∩ F ⁻¹' ((pairCone d : Set (H d × H d)) ×ˢ Iic K)
  have hCc : IsClosed C := hFc.preimage_isClosed_of_isClosed hBc.isClosed
    (isClosed_pairCone.prod isClosed_Iic)
  have hCcompact : IsCompact C := hBc.of_isClosed_subset hCc inter_subset_left
  have hCm (z : Point d) : z ∈ C ↔ z ∈ B ∧ z ∈ feasible S η ∧ objective ε z ≤ K := by
    simp only [C, mem_inter_iff, mem_preimage, mem_prod, mem_Iic, F]
    constructor
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, (feasible_iff_cone S η z).mpr ⟨hBD hz, hc⟩, hf⟩
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, ((feasible_iff_cone S η z).mp hc).2, hf⟩
  have hnonempty : C.Nonempty := by
    refine ⟨z₀, (hCm z₀).mpr ⟨?_, hz₀, hf₀⟩⟩
    exact sublevel_box S η hη hε hK hS₁ hS₂ hz₀ hf₀
  obtain ⟨z, hz, hmin⟩ := hCcompact.exists_isMinOn hnonempty (continuous_objective ε).continuousOn
  have hzm := (hCm z).mp hz
  refine ⟨z, hzm.2.1, hzm.2.2, fun w hw => ?_⟩
  by_cases hfw : objective ε w ≤ K
  · apply hmin
    exact (hCm w).mpr ⟨sublevel_box S η hη hε hK hS₁ hS₂ hw hfw, hw, hfw⟩
  · exact hzm.2.2.trans (le_of_lt (lt_of_not_ge hfw))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_rd39747_2 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

lemma psi_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hr : 0 ≤ 1-x^2 := by have hh := abs_le.mp hx; nlinarith
  exact ⟨Real.rpow_nonneg hr _, Real.rpow_le_one hr (by nlinarith [sq_nonneg x]) (by norm_num)⟩

lemma eta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {x : Coordinates N} (hx : Cube x) :
    ∀ Z ∈ psdCone d, eta c A x Z ∈ psdCone d := by
  intro Z hZ
  rw [eta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (psi_bounds (hx i)).1)

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

lemma eta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i, sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {x : Coordinates N} (hx : Cube x) : eta c A x (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [eta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (psi_bounds (hx i)).2)

end CurrentKS.State

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma scalar_feasible (S : H d) (η : H d →L[ℝ] H d) {s b a : ℝ}
    (hs₁ : -s • (Hermitian.one : H d) ≤ S) (hs₂ : S ≤ s • (Hermitian.one : H d))
    (hb : η (Hermitian.one : H d) ≤ b • (Hermitian.one : H d)) (ha : 0 < a) :
    (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) ∈ feasible S η := by
  have hpd := pd_smul (show (Hermitian.one : H d) ∈ pd d from Matrix.PosDef.one) ha
  apply (feasible_iff _ _ _).mpr
  refine ⟨hpd,hpd,?_,?_⟩
  · change invH (a • (Hermitian.one : H d)) + S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        show a⁻¹ • (Hermitian.one : H d) + S + a • η (Hermitian.one : H d) ≤ _ from
          add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hs₂) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring
  · change invH (a • (Hermitian.one : H d)) - S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    have hns : -S ≤ s • (Hermitian.one : H d) := by
      have hh := neg_le_neg hs₁
      rw [neg_smul s (Hermitian.one : H d), neg_neg] at hh
      exact hh
    change a⁻¹ • (Hermitian.one : H d) + -S + a • η (Hermitian.one : H d) ≤ _
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hns) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring

lemma scalar_objective (ε s b a : ℝ) :
    objective ε (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) =
      s+a⁻¹+(b+2*d*ε)*a := by
  simp only [objective,realTrace_add,realTrace_smul,realTrace_one]
  ring

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormalizedMinimizer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

theorem normalized_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε*d ≤ 1) (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d))
    (hηI : η (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ∃ z ∈ feasible S η,objective ε z ≤ 100 ∧
      ∀ w ∈ feasible S η,objective ε z ≤ objective ε w := by
  have hlo' : -(100:ℝ) • (Hermitian.one : H d) ≤ S := by
    apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  have hhi' : S ≤ (100:ℝ) • (Hermitian.one : H d) := by
    apply hhi.trans
    simpa only [one_smul] using scalar_mono_psd one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)
  let z₀ : Point d := (1+(1/20:ℝ)⁻¹+384*(1/20),(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • (Hermitian.one : H d))
  have hz₀ : z₀ ∈ feasible S η :=
    scalar_feasible S η (s:=1) (b:=384) (a:=1/20)
      (by rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul]; exact hlo)
      (by simpa only [one_smul] using hhi) hηI (by norm_num)
  have hf : objective ε z₀ ≤ 100 := by
    dsimp [z₀]
    rw [scalar_objective]
    norm_num
    nlinarith
  exact exists_minimizer S η hη hε (by norm_num) hlo' hhi' z₀ hz₀ hf
end CurrentKS.Variational

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

lemma coarseBudget_bounds {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    1 ≤ coarseBudget d N ε σ ∧ (d:ℝ)+1 ≤ coarseBudget d N ε σ ∧
    |ε| ≤ coarseBudget d N ε σ ∧
    200+(200/ε)*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    200*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    ((d:ℝ)+1)+N ≤ coarseBudget d N ε σ ∧
    384*N*(1+800/σ^3) ≤ coarseBudget d N ε σ := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  have hr : 0 ≤ 384*(N:ℝ)*(1+800/σ^3) := by positivity
  have he := abs_nonneg ε
  dsimp [coarseBudget]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

end
end CurrentKS.State

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
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SquareInterval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

lemma squareInterval_spec (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^2) (k : ℕ) :
    0 ≤ (squareInterval q k).1 ∧ (squareInterval q k).2 ≤ 1 ∧
    ((squareInterval q k).1:ℝ) ≤ r ∧ r ≤ ((squareInterval q k).2:ℝ) ∧
    (squareInterval q k).2-(squareInterval q k).1=(1/2:ℚ)^k := by
  induction k with
  | zero => simpa [squareInterval] using And.intro hr hr1
  | succ k ih =>
    have horder : (squareInterval q k).1 ≤ (squareInterval q k).2 := by
      exact_mod_cast ih.2.2.1.trans ih.2.2.2.1
    let m : ℚ := ((squareInterval q k).1+(squareInterval q k).2)/2
    have hml : (squareInterval q k).1 ≤ m := by dsimp [m] <;> linarith
    have hmu : m ≤ (squareInterval q k).2 := by dsimp [m] <;> linarith
    have hm : 0 ≤ m := ih.1.trans hml
    have hmr : (0:ℝ) ≤ m := by exact_mod_cast hm
    have he : squareInterval q (k+1) = if m^2 ≤ q then (m,(squareInterval q k).2) else ((squareInterval q k).1,m) := rfl
    rw [he]
    split
    · rename_i h
      have hc : (m:ℝ)^2 ≤ r^2 := by rw [← hq]; exact_mod_cast h
      have hle := (pow_le_pow_iff_left₀ hmr hr (by decide : 2≠0)).mp hc
      refine ⟨hm,ih.2.1,hle,ih.2.2.2.1,?_⟩
      change (squareInterval q k).2-m=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring
    · rename_i h
      have hc : r^2 ≤ (m:ℝ)^2 := by rw [← hq]; exact_mod_cast (le_of_lt (lt_of_not_ge h))
      have hle := (pow_le_pow_iff_left₀ hr hmr (by decide : 2≠0)).mp hc
      refine ⟨ih.1,hmu.trans ih.2.1,ih.2.2.1,hle,?_⟩
      change m-(squareInterval q k).1=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring

lemma squareInterval_upper_error (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^2) (k : ℕ) :
    |((squareInterval q k).2:ℝ)-r| ≤ (1/2:ℝ)^k := by
  obtain ⟨_,_,hl,hu,hw⟩ := squareInterval_spec q r hr hr1 hq k
  have hwr : ((squareInterval q k).2:ℝ)-(squareInterval q k).1=(1/2:ℝ)^k := by
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hw
    norm_num only [Rat.cast_sub,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hc
    exact hc
  rw [abs_of_nonneg (sub_nonneg.mpr hu)]
  linarith

lemma inverse_pow_size_le {δ : ℚ} (hδ : 0 < δ) : (1/2:ℚ)^δ.den.size ≤ δ := by
  have hd : (0:ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hp : (0:ℚ) < 2^δ.den.size := by positivity
  have hnum : (1:ℚ) ≤ δ.num := by exact_mod_cast (Int.add_one_le_iff.mpr (Rat.num_pos.mpr hδ))
  have hden : (δ.den:ℚ) ≤ 2^δ.den.size := by exact_mod_cast (Nat.lt_size_self δ.den).le
  rw [_root_.one_div_pow,one_div]
  calc
    (2^δ.den.size:ℚ)⁻¹ ≤ (δ.den:ℚ)⁻¹ := inv_anti₀ hd hden
    _ ≤ (δ.num:ℚ)/(δ.den:ℚ) := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hnum hd.le
    _ = δ := Rat.num_div_den δ

theorem upperSqrt_spec (q δ : ℚ) (hδ : 0 < δ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.sqrt (q:ℝ) ≤ (upperSqrt q δ:ℝ) ∧
    (upperSqrt q δ:ℝ) ≤ Real.sqrt (q:ℝ)+(δ:ℝ) := by
  have hr := Real.sqrt_nonneg (q:ℝ)
  have hr1 : Real.sqrt (q:ℝ) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr (by exact_mod_cast hq1)
  have he : (q:ℝ) = Real.sqrt (q:ℝ)^2 := (Real.sq_sqrt (by exact_mod_cast hq)).symm
  have hs := squareInterval_spec q (Real.sqrt q) hr hr1 he δ.den.size
  have herror := squareInterval_upper_error q (Real.sqrt q) hr hr1 he δ.den.size
  have hh : (1/2:ℝ)^δ.den.size ≤ (δ:ℝ) := by
    have h := Rat.cast_le (K := ℝ).mpr (inverse_pow_size_le hδ)
    norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at h
    exact h
  refine ⟨hs.2.2.2.1,?_⟩
  have hm := (abs_le.mp herror).2
  dsimp [upperSqrt]
  linarith

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_SqSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open scoped BigOperators

variable {N : ℕ}

lemma sqSum_nonneg (v : Fin N → ℚ) : 0 ≤ sqSum v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sqSum_pos (v : Fin N → ℚ) (hv : v ≠ 0) : 0 < sqSum v := by
  have he : ∃ i,v i ≠ 0 := by
    by_contra! h
    apply hv
    funext i
    exact h i
  obtain ⟨i,hi⟩ := he
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩

lemma sqSum_initialScale (v : Fin N → ℚ) :
    sqSum (initialScale v)=sqSum v/(1+sqSum v)^2 := by
  simp only [sqSum,initialScale,div_pow,Finset.sum_div]

lemma initialScale_spec (v : Fin N → ℚ) (hv : v ≠ 0) :
    0 < sqSum (initialScale v) ∧ sqSum (initialScale v) ≤ 1 := by
  have h := sqSum_pos v hv
  have hr : (0:ℚ)<1+sqSum v := by linarith
  rw [sqSum_initialScale]
  refine ⟨div_pos h (sq_pos_of_pos hr),?_⟩
  apply (div_le_one (sq_pos_of_pos hr)).mpr
  nlinarith [sq_nonneg (sqSum v)]

lemma norm_realVector (v : Fin N → ℚ) : ‖realVector v‖=Real.sqrt (sqSum v:ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp only [realVector,WithLp.ofLp_toLp,Real.norm_eq_abs,sq_abs,sqSum,Rat.cast_sum,Rat.cast_pow]

lemma realVector_div (v : Fin N → ℚ) (r : ℚ) :
    realVector (fun i => v i/r) = ((r:ℝ)⁻¹) • realVector v := by
  apply PiLp.ext
  intro i
  simp only [realVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,Rat.cast_div]
  ring

theorem normalize_spec (v : Fin N → ℚ) (hv : v ≠ 0) (β : ℚ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1-(β:ℝ) ≤ ‖realVector (normalize v β)‖ ∧ ‖realVector (normalize v β)‖ ≤ 1 ∧
    ∃ c : ℚ, 0 < c ∧ normalize v β = fun i => c*v i := by
  let u := initialScale v
  let q := sqSum u
  let U := upperSqrt q (β*q)
  have hq := initialScale_spec v hv
  have hqp : (0:ℝ)<q := by exact_mod_cast hq.1
  have hq1 : (q:ℝ)≤1 := by exact_mod_cast hq.2
  have hp : (0:ℝ)<β := by exact_mod_cast hβ
  have hp1 : (β:ℝ)≤1 := by exact_mod_cast hβ1
  have hs := upperSqrt_spec q (β*q) (mul_pos hβ hq.1) hq.1.le hq.2
  have hspos : 0 < Real.sqrt (q:ℝ) := Real.sqrt_pos.mpr hqp
  have hs1 : Real.sqrt (q:ℝ) ≤ 1 := Real.sqrt_le_one.mpr hq1
  have hql : (q:ℝ) ≤ Real.sqrt (q:ℝ) := by
    nlinarith [Real.sq_sqrt hqp.le]
  have hUpos : (0:ℝ)<U := hspos.trans_le hs.1
  have hUposQ : 0 < U := by exact_mod_cast hUpos
  have hUupper : (U:ℝ) ≤ (1+(β:ℝ))*Real.sqrt (q:ℝ) := by
    have he : ((β*q:ℚ):ℝ)=(β:ℝ)*(q:ℝ) := Rat.cast_mul ..
    rw [he] at hs
    nlinarith
  have hn : ‖realVector (normalize v β)‖=Real.sqrt (q:ℝ)/(U:ℝ) := by
    change ‖realVector (fun i => u i/U)‖=_
    rw [realVector_div,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hUpos),norm_realVector]
    ring
  rw [hn]
  refine ⟨?_,(div_le_one hUpos).mpr hs.1,?_⟩
  · apply (le_div_iff₀ hUpos).mpr
    have hu := mul_le_mul_of_nonneg_left hUupper (sub_nonneg.mpr hp1)
    nlinarith [mul_nonneg (sq_nonneg (β:ℝ)) hspos.le]
  · have hr : (0:ℚ)<1+sqSum v := by linarith [sqSum_nonneg v]
    refine ⟨((1+sqSum v)*U)⁻¹,inv_pos.mpr (mul_pos hr hUposQ),?_⟩
    funext i
    change (v i/(1+sqSum v))/U=((1+sqSum v)*U)⁻¹*v i
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NegativeDirection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot

section
open Matrix
open scoped BigOperators

variable {N : ℕ}

lemma quadratic_scale (M : Matrix (Fin N) (Fin N) ℚ) (v : Fin N → ℚ) (c : ℚ) :
    (fun i => c*v i) ⬝ᵥ (M *ᵥ (fun i => c*v i)) = c^2*(v ⬝ᵥ (M *ᵥ v)) := by
  simp only [dotProduct,mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem negativeDirection_spec (M : Matrix (Fin N) (Fin N) ℚ) (hM : M.IsSymm)
    (β : ℚ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    match negativeDirection M β with
    | none => (M.map (fun q : ℚ => (q:ℝ))).PosSemidef
    | some w => 1-(β:ℝ) ≤ ‖realVector w‖ ∧ ‖realVector w‖ ≤ 1 ∧ w ⬝ᵥ (M *ᵥ w) < 0 := by
  unfold negativeDirection
  cases he : KS.W17.rationalNegativeWitness N M with
  | none => exact KS.W17.rationalNegativeWitness_none_psd N M hM he
  | some v =>
    simp only [Option.map_some]
    have hv := KS.W17.rationalNegativeWitness_sound N M hM v he
    have hv0 : v ≠ 0 := by
      intro h
      simp only [h,Matrix.mulVec_zero,dotProduct_zero] at hv
      exact (lt_irrefl 0 hv)
    obtain ⟨hl,hu,c,hc,hwe⟩ := normalize_spec v hv0 β hβ hβ1
    refine ⟨hl,hu,?_⟩
    rw [hwe,quadratic_scale]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hc) hv
end

open scoped BigOperators

variable {N : ℕ}

lemma nearest_error (t : ℚ) : |(nearest t:ℚ)-t| ≤ 1/2 := by
  unfold nearest
  split_ifs with ht
  · have hl := Int.le_ceil (t-1/2)
    have hu := Int.ceil_lt_add_one (t-1/2)
    rw [abs_le]
    constructor <;> linarith
  · have hl := Int.le_ceil (-t-1/2)
    have hu := Int.ceil_lt_add_one (-t-1/2)
    rw [Int.cast_neg,abs_le]
    constructor <;> linarith

lemma roundMesh_coord_error (ρ : ℚ) (hρ : 0 < ρ) (v : Fin N → ℚ) (i : Fin N) :
    |roundMesh ρ v i-v i| ≤ ρ/2 := by
  have he : roundMesh ρ v i-v i=ρ*((nearest (v i/ρ):ℚ)-v i/ρ) := by
    dsimp [roundMesh]
    field_simp
  rw [he,abs_mul,abs_of_pos hρ]
  exact (mul_le_mul_of_nonneg_left (nearest_error _) hρ.le).trans_eq (by ring)

lemma norm_le_sum_abs (v : EuclideanSpace ℝ (Fin N)) : ‖v‖ ≤ ∑ i,|v i| := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  simpa only [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun i _ => abs_nonneg (v i))

lemma roundMesh_error (ρ : ℚ) (hρ : 0 < ρ) (v : Fin N → ℚ) :
    ‖realVector (roundMesh ρ v)-realVector v‖ ≤ N*(ρ:ℝ)/2 := by
  apply (norm_le_sum_abs _).trans
  calc
    (∑ i, |(realVector (roundMesh ρ v)-realVector v) i|) ≤ ∑ _ : Fin N,(ρ:ℝ)/2 := by
      apply Finset.sum_le_sum
      intro i _
      change |(roundMesh ρ v i:ℝ)-(v i:ℝ)| ≤ (ρ:ℝ)/2
      exact_mod_cast roundMesh_coord_error ρ hρ v i
    _ = N*(ρ:ℝ)/2 := by simp <;> ring

lemma realVector_scale (v : Fin N → ℚ) (c : ℚ) :
    realVector (fun i => c*v i)=(c:ℝ) • realVector v := by
  apply PiLp.ext
  intro i
  simp only [realVector,WithLp.ofLp_toLp,PiLp.smul_apply,smul_eq_mul,Rat.cast_mul]

theorem curvature_rounding (w : Fin N → ℚ) (s τ ρ : ℚ)
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*τ/8) (hw : ‖realVector w‖ ≤ 1) :
    let q := roundMesh ρ (fun i => s*(1-τ)*w i)
    ‖realVector q-((s:ℝ)*(1-(τ:ℝ))) • realVector w‖ ≤ (s:ℝ)*τ/8 ∧
    ‖realVector q‖ ≤ s ∧
    ‖realVector q-(s:ℝ) • realVector w‖ ≤ 9*(s:ℝ)*τ/8 := by
  let q := roundMesh ρ (fun i => s*(1-τ)*w i)
  have hs' : (0:ℝ) ≤ s := by exact_mod_cast hs
  have ht' : (0:ℝ) ≤ τ := by exact_mod_cast hτ
  have ht1' : (τ:ℝ) ≤ 1 := by exact_mod_cast hτ1
  have hm : (N:ℝ)*(ρ:ℝ)/2 ≤ (s:ℝ)*τ/8 := by exact_mod_cast hmesh
  have he := (roundMesh_error ρ hρ (fun i => s*(1-τ)*w i)).trans hm
  rw [realVector_scale] at he
  push_cast at he
  have ht : ‖((s:ℝ)*(1-(τ:ℝ))) • realVector w‖ ≤ (s:ℝ)*(1-(τ:ℝ)) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hs' (sub_nonneg.mpr ht1'))]
    exact mul_le_of_le_one_right (mul_nonneg hs' (sub_nonneg.mpr ht1')) hw
  have hqn : ‖realVector q‖ ≤ s := by
    have hb := norm_le_norm_sub_add (realVector q) (((s:ℝ)*(1-(τ:ℝ))) • realVector w)
    nlinarith [mul_nonneg hs' ht']
  refine ⟨he,hqn,?_⟩
  have hd : ‖((s:ℝ)*(1-(τ:ℝ))) • realVector w-(s:ℝ) • realVector w‖ ≤ (s:ℝ)*τ := by
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    have hx : (s:ℝ)*(1-(τ:ℝ))-(s:ℝ) = -((s:ℝ)*τ) := by ring
    rw [hx,abs_neg,abs_of_nonneg (mul_nonneg hs' ht')]
    exact mul_le_of_le_one_right (mul_nonneg hs' ht') hw
  have hb := norm_sub_le_norm_sub_add_norm_sub (realVector q) (((s:ℝ)*(1-(τ:ℝ))) • realVector w) ((s:ℝ) • realVector w)
  linarith
end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_ShiftedHessian
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open Matrix CurrentKS.Difference
open scoped BigOperators

variable {N : ℕ}

lemma shiftedHessian_symm (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm) (a : ℚ) :
    (shiftedHessian H a).IsSymm := by
  exact hH.add (isSymm_one.smul _)

lemma curvature_parameters {a M : ℚ} (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) :
    0 < a/(4096*M) ∧ a/(4096*M)≤1 ∧ 0 ≤ a/(1024*M) ∧ a/(1024*M)≤1 := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨by positivity,?_,by positivity,?_⟩
  · apply (div_le_one (by positivity : (0:ℚ)<4096*M)).mpr
    linarith
  · apply (div_le_one (by positivity : (0:ℚ)<1024*M)).mpr
    linarith

end CurrentKS.RationalRoot

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Select
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent
variable {α : Type*}

lemma select_mem (score : α → ℚ) (a : α) (l : List α) : select score a l ∈ a :: l := by
  induction l generalizing a with
  | nil => simp [select]
  | cons b bs ih =>
    rw [select]
    split
    · have hh := ih b
      simp only [List.mem_cons] at hh ⊢
      tauto
    · have hh := ih a
      simp only [List.mem_cons] at hh ⊢
      tauto

lemma select_le (score : α → ℚ) (a : α) (l : List α) :
    ∀ b ∈ a :: l, score (select score a l) ≤ score b := by
  induction l generalizing a with
  | nil => simp [select]
  | cons b bs ih =>
    rw [select]
    split
    · rename_i h
      intro c hc
      have hb := ih b b (by simp)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact hb.trans h.le
      · exact hb
      · exact ih b c (by simp [hc])
    · rename_i h
      intro c hc
      have ha := ih a a (by simp)
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact ha
      · exact ha.trans (le_of_not_gt h)
      · exact ih a c (by simp [hc])

theorem select_value_bound (f : α → ℝ) (score : α → ℚ) (a : α) (l : List α)
    {e : ℝ} (herr : ∀ b ∈ a :: l, |(score b:ℝ)-f b| ≤ e) :
    ∀ b ∈ a :: l, f (select score a l) ≤ f b+2*e := by
  intro b hb
  have hs := abs_le.mp (herr (select score a l) (select_mem score a l))
  have ht := abs_le.mp (herr b hb)
  have hm : (score (select score a l):ℝ) ≤ (score b:ℝ) := by exact_mod_cast select_le score a l b hb
  linarith

theorem select_decrease (f : α → ℝ) (score : α → ℚ) (x a : α) (l : List α)
    {Δ : ℝ} (herr : ∀ b ∈ a :: l, |(score b:ℝ)-f b| ≤ Δ/4)
    (hgood : ∃ b ∈ a :: l, f b ≤ f x-2*Δ) :
    f (select score a l) ≤ f x-3*Δ/2 := by
  obtain ⟨b,hb,hf⟩ := hgood
  have hs := select_value_bound f score a l herr b hb
  linarith

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ChooseCoordinate
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference

open Set
open scoped ContDiff

variable {N : ℕ}

lemma rationalGradientDirection_cast [NeZero N] (g : Fin N → ℚ) :
    (fun i => (rationalGradientDirection g i:ℝ))=gradientDirection g := by
  classical
  funext j
  simp only [rationalGradientDirection,gradientDirection,Pi.smul_apply,smul_eq_mul,
    Rat.cast_mul,Pi.single_apply]
  split_ifs <;> norm_num

lemma gradientDirection_bound [NeZero N] (g : Fin N → ℚ) : ‖gradientDirection g‖ ≤ 1 := by
  classical
  unfold gradientDirection
  split_ifs <;> simp only [neg_smul,one_smul,norm_neg]
  all_goals
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i=chooseCoordinate g <;> simp [hi]

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_RationalBasis
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open Set Matrix
open scoped BigOperators ContDiff

variable {N : ℕ}

lemma pointCast_step (x v : Fin N → ℚ) (h : ℚ) :
    pointCast (x+h • v)=pointCast x+(h:ℝ) • pointCast v := by
  funext i
  simp [pointCast]

lemma pointCast_add (u v : Fin N → ℚ) : pointCast (u+v)=pointCast u+pointCast v := by
  funext i
  simp [pointCast]

lemma stencilHessian_symm (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h : ℚ) :
    (stencilHessian query x h).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  dsimp [stencilHessian]
  by_cases hij : i=j
  · subst j; rfl
  · rw [ite_eq_right hij,ite_eq_right (Ne.symm hij)]
    have h1 : rationalBasis j+rationalBasis i=rationalBasis i+rationalBasis j := add_comm _ _
    have h2 : rationalBasis j-rationalBasis i = -rationalBasis i+rationalBasis j := sub_eq_neg_add _ _
    have h3 : -rationalBasis j+rationalBasis i=rationalBasis i-rationalBasis j := (sub_eq_neg_add _ _).symm
    have h4 : -rationalBasis j-rationalBasis i = -rationalBasis i-rationalBasis j := by
      simp only [sub_eq_add_neg,add_comm]
    rw [h1,h2,h3,h4]
    ring

lemma pointCast_sub (u v : Fin N → ℚ) : pointCast (u-v)=pointCast u-pointCast v := by
  funext i
  simp [pointCast]

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EuclideanForget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open scoped ContDiff

variable {N : ℕ}

lemma euclideanForget_bound (u : EuclideanSpace ℝ (Fin N)) : ‖euclideanForget u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact PiLp.norm_apply_le u i

open CurrentKS.RationalRoot Matrix Set

lemma pointCast_gradient [NeZero N] (x g : Fin N → ℚ) (s : ℚ) :
    pointCast (x+s • rationalGradientDirection g)=pointCast x+(s:ℝ) • gradientDirection g := by
  rw [pointCast_step]
  have hh : pointCast (rationalGradientDirection g)=gradientDirection g := rationalGradientDirection_cast g
  rw [hh]

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EndpointCandidates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalRoot
open Matrix

variable {N : ℕ}

lemma computedCurvature_norm (H : Matrix (Fin N) (Fin N) ℚ) (hH : H.IsSymm)
    (a M s ρ : ℚ) (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) (q : Fin N → ℚ)
    (hq : computedCurvature H a M s ρ=some q) : ‖realVector q‖ ≤ (s:ℝ) := by
  have hpar := curvature_parameters ha ha1 hM
  have hd := negativeDirection_spec (shiftedHessian H a) (shiftedHessian_symm H hH a)
    (a/(4096*M)) hpar.1 hpar.2.1
  unfold computedCurvature at hq
  cases he : negativeDirection (shiftedHessian H a) (a/(4096*M)) with
  | none => simp [he] at hq
  | some w =>
    simp only [he] at hd
    simp only [he,Option.map_some,Option.some.injEq] at hq
    subst q
    exact (curvature_rounding w s (a/(1024*M)) ρ hs hpar.2.2.1 hpar.2.2.2 hρ hmesh hd.2.1).2.1

end CurrentKS.RationalRoot

namespace CurrentKS.Difference
open CurrentKS.RationalRoot

variable {N : ℕ}

lemma interiorCandidates_distance [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ : ℚ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) :
    ∀ y∈interiorCandidates query x h a M s ρ,‖pointCast y-pointCast x‖ ≤ (s:ℝ) := by
  intro y hy
  simp only [interiorCandidates,List.mem_cons] at hy
  rcases hy with rfl|hy
  · rw [pointCast_gradient,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ) ≤ s by exact_mod_cast hs)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (gradientDirection_bound (stencilGradient query x h)) (show (0:ℝ) ≤ s by exact_mod_cast hs)
  · cases he : computedCurvature (stencilHessian query x h) a M s ρ with
    | none => simp [he] at hy
    | some q =>
      have hb := (euclideanForget_bound (realVector q)).trans
        (computedCurvature_norm _ (stencilHessian_symm query x h) a M s ρ ha ha1 hM hs hρ hmesh q he)
      change ‖pointCast q‖ ≤ (s:ℝ) at hb
      simp only [he,List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl
      · simpa only [pointCast_add,add_sub_cancel_left] using hb
      · simpa only [pointCast_sub,sub_sub_cancel_left,norm_neg] using hb

lemma endpointCandidates_cube (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    ∀ y∈endpointCandidates x,∀ i,|y i| ≤ 1 := by
  intro y hy j
  obtain ⟨i,_,hy⟩ := List.mem_flatMap.mp hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl
  all_goals
    by_cases hji : j=i
    · subst j;simp
    · simpa only [Function.update_of_ne hji] using hx j

lemma allCandidates_cube [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (h a M s ρ σ : ℚ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hM : 1 ≤ M) (hs : 0 ≤ s) (hρ : 0 < ρ)
    (hmesh : (N:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8) (hsσ : s ≤ σ)
    (_hσ : 0 ≤ σ) (hx : ∀ i,|x i| ≤ 1-σ) :
    ∀ y∈allCandidates query x h a M s ρ,∀ i,|y i| ≤ 1 := by
  intro y hy
  rcases List.mem_append.mp hy with he|hi
  · exact endpointCandidates_cube x (fun i => (hx i).trans (by linarith)) y he
  · have hd := interiorCandidates_distance query x h a M s ρ ha ha1 hM hs hρ hmesh y hi
    intro i
    have hb := (pi_norm_le_iff_of_nonneg (show (0:ℝ) ≤ s by exact_mod_cast hs)).mp hd i
    change ‖(y i:ℝ)-(x i:ℝ)‖ ≤ (s:ℝ) at hb
    rw [Real.norm_eq_abs] at hb
    have hc : |(x i:ℝ)| ≤ 1-(σ:ℝ) := by exact_mod_cast hx i
    have hd' : (s:ℝ) ≤ (σ:ℝ) := by exact_mod_cast hsσ
    have htri : |(y i:ℝ)| ≤ |(y i:ℝ)-(x i:ℝ)|+|(x i:ℝ)| := by
      simpa only [sub_zero] using abs_sub_le (y i:ℝ) (x i:ℝ) 0
    have hh : |(y i:ℝ)| ≤ 1 := by linarith
    exact_mod_cast hh

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FacePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


lemma valueCurve_bounds_nonneg {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    0 ≤ valueCurve2Bound d N ε σ ∧ 0 ≤ valueCurve3Bound d N ε σ := by
  have hB := (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  dsimp [valueCurve2Bound,valueCurve3Bound]
  constructor <;> positivity

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Potential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
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

lemma sum_update_composite {α β : Type*} [AddCommGroup β] (f : Fin N → α → β)
    (x : Fin N → α) (i : Fin N) (a : α) :
    (∑ j, f j (Function.update x i a j)) = (∑ j, f j (x j))+f i a-f i (x i) := by
  simp only [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have he := Finset.sum_erase_add Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← he]
  abel

lemma S_update (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) :
    S A (Function.update x i t) = S A x+(t-x i) • A i := by
  rw [S,sum_update_composite (fun (j : Fin N) (r : ℝ) => r • A j) x i t]
  simp only [S]
  module

lemma eta_update (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) (Z : H d) :
    eta c A (Function.update x i t) Z = eta c A x Z+(c*(psi t-psi (x i))) • sandwich (A i) Z := by
  rw [eta_apply,sum_update_composite (fun (j : Fin N) (r : ℝ) => (c*psi r) • sandwich (A j) Z) x i t,eta_apply]
  module

lemma psi_endpoint {t : ℝ} (ht : |t| = 1) : psi t = 0 := by
  have hh : t^2 = 1 := by nlinarith [sq_abs t]
  simp [psi,hh]

lemma Cube_update {x : Coordinates N} (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t| ≤ 1) :
    Cube (Function.update x i t) := by
  intro j
  by_cases hj : j=i
  · subst j; simpa using ht
  · simpa [Function.update_of_ne hj] using hx j

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma movementBudget_one_le (n : ℕ) (ε : ℚ) : 1 ≤ movementBudget n ε := le_max_left _ _

lemma movementBudget_pos (n : ℕ) (ε : ℚ) : 0 < movementBudget n ε :=
  lt_of_lt_of_le (by norm_num) (movementBudget_one_le n ε)

lemma threshold_pos (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : 0 < lam) : 0 < threshold n ε lam := by
  unfold threshold
  have hp := movementBudget_pos n ε
  positivity

lemma threshold_le_one (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : lam ≤ 1) : threshold n ε lam ≤ 1 := by
  unfold threshold
  have hp := movementBudget_pos n ε
  have h1 := movementBudget_one_le n ε
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma stepSize_spec {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stepSize a M σ ∧ stepSize a M σ ≤ σ/4 ∧ stepSize a M σ ≤ 1/4 ∧
      M*stepSize a M σ ≤ a/4 := by
  have hp : 0 < a/(4*M) := by positivity
  have hs : stepSize a M σ ≤ a/(4*M) := min_le_right _ _ |>.trans (min_le_left _ _)
  refine ⟨by unfold stepSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_right _ _),?_⟩
  have hh := (le_div_iff₀ (show (0:ℚ) < 4*M by positivity)).mp hs
  linarith

lemma stencilSize_spec {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stencilSize n a M σ ∧ stencilSize n a M σ ≤ σ/8 ∧
    stencilSize n a M σ ≤ 1 ∧ stencilSize n a M σ ≤ a/(64*M*n) := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold stencilSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

lemma meshSize_spec {n : ℕ} (hn : 0 < n) {a M s : ℚ} (ha : 0 < a) (hM : 0 < M) (hs : 0 < s) :
    0 < meshSize n a M s ∧ (n:ℚ)*meshSize n a M s/2 ≤ s*(a/(1024*M))/8 := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold meshSize;positivity,?_⟩
  unfold meshSize
  apply le_of_eq
  field_simp
  ring

lemma schedule_radius {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    stepSize a M σ+2*stencilSize n a M σ ≤ σ/2 := by
  have hs := (stepSize_spec ha hM hσ).2.1
  have hh := (stencilSize_spec hn ha hM hσ).2.1
  linarith

open CurrentKS.State

lemma coarseBudgetQ_cast (d n : ℕ) (ε σ : ℚ) :
    (coarseBudgetQ d n ε σ:ℝ)=coarseBudget d n (ε:ℝ) (σ:ℝ) := by
  simp only [coarseBudgetQ,coarseBudget,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_abs,Rat.cast_ofNat,Rat.cast_one]

lemma curveBudget_cast (d n : ℕ) (ε σ lam : ℚ) :
    (curveBudget d n ε σ lam:ℝ)=potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
  simp only [curveBudget,potentialCurveBound,valueCurve2Q,valueCurve3Q,
    valueCurve2Bound,valueCurve3Bound,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_abs,Rat.cast_inv,Rat.cast_one,Rat.cast_ofNat,coarseBudgetQ_cast]

lemma curveBudget_one_le (d n : ℕ) {ε σ : ℚ} (hε : 0 < ε) (hσ : 0 < σ) (lam : ℚ) :
    1 ≤ curveBudget d n ε σ lam := by
  have hεr : (0:ℝ) < ε := by exact_mod_cast hε
  have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
  have hh := valueCurve_bounds_nonneg (d:=d) (N:=n) hεr hσr
  have hl : (0:ℝ) ≤ |(lam:ℝ)| *(n:ℝ)*(1+800/(σ:ℝ)^3) := by positivity
  have hc : (1:ℝ) ≤ potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
    unfold potentialCurveBound
    linarith
  rw [←curveBudget_cast] at hc
  exact_mod_cast hc

end CurrentKS.Schedule

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

lemma extend_self {β : Type*} (e : Fin n → Fin N) (base : Fin N → β) :
    extend e base (fun j => base (e j))=base := by
  funext i
  unfold extend
  cases hh : lookup e i with
  | none => rfl
  | some j => simp only [Option.elim_some,lookup_some hh]

lemma map_extend {β γ : Type*} (f : β → γ) (e : Fin n → Fin N)
    (base : Fin N → β) (y : Fin n → β) :
    (fun i => f (extend e base y i))=extend e (fun i => f (base i)) (fun j => f (y j)) := by
  funext i
  unfold extend
  cases lookup e i <;> rfl

lemma activeIndices_mem (x : Fin N → ℚ) (i : Fin N) :
    i∈activeIndices x ↔ |x i|<1 := by simp [activeIndices]

lemma activeIndex_injective (x : Fin N → ℚ) : Function.Injective (activeIndex x) := by
  exact ((List.nodup_finRange N).filter _).injective_get

lemma activeIndex_range (x : Fin N → ℚ) (i : Fin N) :
    (∃ j,activeIndex x j=i) ↔ |x i|<1 := by
  rw [←activeIndices_mem]
  exact List.mem_iff_get.symm

lemma activeIndex_interior (x : Fin N → ℚ) (j : Fin (activeIndices x).length) :
    |x (activeIndex x j)|<1 := (activeIndex_range x _).mp ⟨j,rfl⟩

lemma activeIndices_length_le (x : Fin N → ℚ) : (activeIndices x).length≤N := by
  have hh := List.length_filter_le (fun i : Fin N => decide (|x i|<1)) (List.finRange N)
  simp only [List.length_finRange] at hh
  exact hh

lemma extend_cube {e : Fin n → Fin N} (x : Fin N → ℚ) (y : Fin n → ℚ)
    (hx : ∀ i,|x i|≤1) (hy : ∀ j,|y j|≤1) : ∀ i,|extend e x y i|≤1 := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hx i
  | some j => exact hy j

lemma sum_lookup {β : Type*} [AddCommMonoid β] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → Fin n → β) :
    (∑ i,(lookup e i).elim 0 (f i))=∑ j,f (e j) j := by
  symm
  apply Fintype.sum_of_injective e he
  · intro i hi
    have hn : ∀ j,e j≠i := fun j hj => hi ⟨j,hj⟩
    simp only [(lookup_none_iff e i).mpr hn,Option.elim_none]
  · intro j
    simp only [lookup_self he,Option.elim_some]

lemma sum_extend {β γ : Type*} [AddCommMonoid γ] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → β → γ) (base : Fin N → β) (y : Fin n → β) :
    (∑ i,f i (extend e base y i))=
      (∑ i,(lookup e i).elim (f i (base i)) (fun _ => 0))+(∑ j,f (e j) (y j)) := by
  rw [←sum_lookup e he (fun i j => f i (y j)),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold extend
  cases lookup e i <;> simp

lemma real_active_outside_endpoint (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N)
    (hi : lookup (activeIndex x) i=none) : |(x i:ℝ)|=1 := by
  have hn : ¬|x i|<1 := by
    intro h
    obtain ⟨j,hj⟩ := (activeIndex_range x i).mpr h
    exact (lookup_none_iff _ _).mp hi j hj
  have he : |x i|=1 := le_antisymm (hx i) (le_of_not_gt hn)
  exact_mod_cast he

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ParameterCube
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
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

lemma parameterCube_psi {x : Coordinates N} (hx : Cube x) : ParameterCube (fun i => psi (x i)) :=
  fun i => psi_bounds (hx i)

lemma etaTheta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {θ : Coordinates N}
    (hθ : ParameterCube θ) : ∀ Z ∈ psdCone d, etaTheta c A θ Z ∈ psdCone d := by
  intro Z hZ
  rw [etaTheta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (hθ i).1)

lemma sandwich_mono_order (A : H d) {U V : H d} (hUV : U ≤ V) : sandwich A U ≤ sandwich A V := by
  apply sub_nonneg.mp
  rw [← sandwich_sub]
  exact psd_nonneg (sandwich_psd A (V-U) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUV)))

lemma etaTheta_difference_le {c ν δ R : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (θ φ : Coordinates N) (hdiff : ∀ i, θ i-φ i ≤ δ)
    (Z : H d) (hZ : Z ∈ psdCone d) (hZR : Z ≤ R • (Hermitian.one : H d)) :
    etaTheta c A θ Z-etaTheta c A φ Z ≤ (c*δ*R*ν) • (Hermitian.one : H d) := by
  have hsum : (∑ i,sandwich (A i) Z) ≤ (R*ν) • (Hermitian.one : H d) := by
    calc
      _ ≤ ∑ i,sandwich (A i) (R • (Hermitian.one : H d)) :=
        Finset.sum_le_sum fun i _ => sandwich_mono_order (A i) hZR
      _ = R • (∑ i,sandwich (A i) (Hermitian.one : H d)) := by
        simp only [sandwich_smul,Finset.smul_sum]
      _ ≤ R • (ν • (Hermitian.one : H d)) := smul_order hν hR
      _ = _ := by rw [smul_smul]
  calc
    _ = ∑ i,(c*(θ i-φ i)) • sandwich (A i) Z := by
      simp only [etaTheta_apply,← Finset.sum_sub_distrib,mul_sub]
      apply Finset.sum_congr rfl
      intro i _
      exact (sub_smul (c*θ i) (c*φ i) (sandwich (A i) Z)).symm
    _ ≤ ∑ i,(c*δ) • sandwich (A i) Z := by
      apply Finset.sum_le_sum
      intro i _
      exact scalar_mono_psd (sandwich_psd _ _ hZ) (mul_le_mul_of_nonneg_left (hdiff i) hc)
    _ = (c*δ) • (∑ i,sandwich (A i) Z) := by rw [Finset.smul_sum]
    _ ≤ (c*δ) • ((R*ν) • (Hermitian.one : H d)) := smul_order hsum (mul_nonneg hc hδ)
    _ = _ := by rw [smul_smul]; congr 1; ring

lemma etaTheta_shift_feasible {c ν δ R : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (θ φ : Coordinates N) (hdiff : ∀ i, φ i-θ i ≤ δ) (S : H d)
    (z : Point d) (hz : z ∈ feasible S (etaTheta c A θ))
    (hX : z.2.1 ≤ R • (Hermitian.one : H d)) (hY : z.2.2 ≤ R • (Hermitian.one : H d)) :
    (z.1+c*δ*R*ν,z.2) ∈ feasible S (etaTheta c A φ) := by
  obtain ⟨hpX,hpY,h₁,h₂⟩ := (feasible_iff _ _ _).mp hz
  refine (feasible_iff _ _ _).mpr ⟨hpX,hpY,?_,?_⟩
  · have hh := etaTheta_difference_le hc hδ hR A hν φ θ hdiff z.2.2 hpY.posSemidef hY
    have hb := add_le_add h₁ hh
    convert hb using 1 <;> first | rfl | module
  · have hh := etaTheta_difference_le hc hδ hR A hν φ θ hdiff z.2.1 hpX.posSemidef hX
    have hb := add_le_add h₂ hh
    convert hb using 1 <;> first | rfl | module

lemma objective_shift (ε t : ℝ) (z : Point d) :
    objective ε (z.1+t,z.2) = objective ε z+t := by simp only [objective] <;> ring

lemma etaTheta_value_le [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν δ : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (hδ : 0 ≤ δ)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ φ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) (hφ : ParameterCube φ)
    (hdiff : ∀ i,θ i-φ i ≤ δ) :
    value (ν/d) (S A x) (etaTheta 384 A θ) ≤
      value (ν/d) (S A x) (etaTheta 384 A φ)+38400*(d : ℝ)*δ := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d : ℝ) := div_pos hν hd
  obtain ⟨z,hz,hz100,hzmin⟩ := etaTheta_minimizer A hA htr hν hν₁ hvar x φ hx hφ
  have hb := S_bounds A hA htr hx
  have hl : -(100 : ℝ) • (Hermitian.one : H d) ≤ S A x :=
    (show -(100 : ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      simpa only [neg_one_smul ℝ (Hermitian.one : H d)] using
        scalar_one_mono (d := d) (show (-100 : ℝ) ≤ -1 by norm_num)).trans hb.1
  have hu : S A x ≤ (100 : ℝ) • (Hermitian.one : H d) := hb.2.trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show (1 : ℝ) ≤ 100 by norm_num))
  have hbox := sublevel_box (S A x) (etaTheta 384 A φ)
    (etaTheta_positive (by norm_num) A hφ) hε (show (0 : ℝ)<100 by norm_num) hl hu hz hz100
  have hshift := etaTheta_shift_feasible (show (0 : ℝ)≤384 by norm_num) hδ
    (show 0 ≤ 100/(ν/(d : ℝ)) by positivity) A hvar φ θ hdiff (S A x) z hz hbox.2.1.2 hbox.2.2.2
  have hmin := value_eq_of_min (ν/d) (S A x) (etaTheta 384 A φ) z hz hzmin
  calc
    _ ≤ objective (ν/d) (z.1+384*δ*(100/(ν/(d : ℝ)))*ν,z.2) :=
      value_le_feasible _ hε.le _ _ (etaTheta_positive (by norm_num) A hθ) _ hshift
    _ = objective (ν/d) z+384*δ*(100/(ν/(d : ℝ)))*ν := objective_shift _ _ _
    _ = _ := by rw [hmin]; congr 1; field_simp <;> ring

lemma sum_parameter_difference_le {θ φ : Coordinates N} {δ : ℝ}
    (h : ∀ i,θ i-φ i ≤ δ) : (∑ i,θ i)-(∑ i,φ i) ≤ (N : ℝ)*δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _ : Fin N,δ := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

lemma etaTheta_value_perturbation [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν δ lam : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ φ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) (hφ : ParameterCube φ)
    (hdiff : ∀ i,|θ i-φ i| ≤ δ) :
    |(value (ν/d) (S A x) (etaTheta 384 A θ)+lam*∑ i,θ i)-
      (value (ν/d) (S A x) (etaTheta 384 A φ)+lam*∑ i,φ i)| ≤
      (38400*(d : ℝ)+lam*N)*δ := by
  have h₁ : ∀ i,θ i-φ i ≤ δ := fun i => (abs_le.mp (hdiff i)).2
  have h₂ : ∀ i,φ i-θ i ≤ δ := fun i => by have h := (abs_le.mp (hdiff i)).1; linarith
  have hv₁ := etaTheta_value_le A hA htr hν hν₁ hδ hvar x θ φ hx hθ hφ h₁
  have hv₂ := etaTheta_value_le A hA htr hν hν₁ hδ hvar x φ θ hx hφ hθ h₂
  have hs₁ := mul_le_mul_of_nonneg_left (sum_parameter_difference_le h₁) hlam
  have hs₂ := mul_le_mul_of_nonneg_left (sum_parameter_difference_le h₂) hlam
  apply abs_le.mpr
  constructor <;> nlinarith

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RootTolerance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State CurrentKS.Scalar
open Matrix Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

lemma rootTolerance_pos {lam error : ℚ} (hlam : 0 ≤ lam) (he : 0 < error) :
    0 < rootTolerance d N lam error := by
  unfold rootTolerance
  positivity

lemma rootTolerance_bound {lam error : ℚ} (hlam : 0 ≤ lam) (he : 0 < error) :
    (38400*d+lam*N)*rootTolerance d N lam error ≤ error/2 := by
  have hD : 0 < (2*(38400*(d:ℚ)+lam*N+1)) := by positivity
  have hpos := rootTolerance_pos (d := d) (N := N) hlam he
  have hid : 2*(38400*(d:ℚ)+lam*N+1)*rootTolerance d N lam error=error := by
    unfold rootTolerance
    field_simp
  nlinarith

theorem potentialQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (x : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (he : 0 < error) (he1 : error ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) :
    |(potentialQuery coords x ν lam error:ℝ)-
      (value ((ν:ℝ)/d) (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (eta 384 (rationalAtoms coords) (fun i => (x i:ℝ)))+
        (lam:ℝ)*∑ i,psi (x i:ℝ))| ≤ (error:ℝ) := by
  let δ := rootTolerance d N lam error
  let θ := fun i => approxPsi (x i) δ
  let xr : Coordinates N := fun i => (x i:ℝ)
  let θr : Coordinates N := fun i => (θ i:ℝ)
  let A := rationalAtoms coords
  have hδ : 0 < δ := rootTolerance_pos hlam he
  have hroot (i : Fin N) := approxPsi_spec (x i) δ (hx i) hδ
  have hθ : ParameterCube θr := by
    intro i
    change 0 ≤ (approxPsi (x i) δ:ℝ) ∧ (approxPsi (x i) δ:ℝ) ≤ 1
    exact ⟨by exact_mod_cast (hroot i).1.1,by exact_mod_cast (hroot i).1.2⟩
  have hdiff : ∀ i,|θr i-psi (xr i)| ≤ (δ:ℝ) := fun i => (hroot i).2
  have hq := (valueQueryPoint_correct coords x θ hA htr hν hν1
    (by positivity : 0 < error/4) (by linarith : error/4 ≤ 1) hvar hx hθ).2
  have hp := etaTheta_value_perturbation A hA htr (ν := (ν:ℝ)) (δ := (δ:ℝ)) (lam := (lam:ℝ)) (by exact_mod_cast hν)
    (by exact_mod_cast hν1) (by exact_mod_cast hδ.le) (by exact_mod_cast hlam)
    hvar xr θr (fun i => psi (xr i)) hx hθ (parameterCube_psi hx) hdiff
  let mid : ℝ := value ((ν:ℝ)/d) (S A xr) (etaTheta 384 A θr)+(lam:ℝ)*∑ i,θr i
  have hqm : |(potentialQuery coords x ν lam error:ℝ)-mid| ≤ (error:ℝ)/2 := by
    dsimp only [potentialQuery,mid]
    push_cast
    have heq : ((ν/d:ℚ):ℝ)=(ν:ℝ)/d := by push_cast; rfl
    simp only [heq,Rat.cast_div,Rat.cast_ofNat] at hq
    convert hq using 1 <;> first | rfl | ((try dsimp [θ,θr,A,xr,δ]); ring_nf)
  have hpm : |mid-(value ((ν:ℝ)/d) (S A xr) (eta 384 A xr)+
      (lam:ℝ)*∑ i,psi (xr i))| ≤ (error:ℝ)/2 := by
    apply hp.trans
    exact_mod_cast rootTolerance_bound (d := d) (N := N) hlam he
  change |(potentialQuery coords x ν lam error:ℝ)-
    (value ((ν:ℝ)/d) (S A xr) (eta 384 A xr)+(lam:ℝ)*∑ i,psi (xr i))| ≤ _
  exact (abs_sub_le _ mid _).trans (by linarith)

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FixedPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N n : ℕ}

lemma S_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d) (y : Coordinates n) :
    S A (extend e base y)=fixedPart e base A+S (fun j => A (e j)) y := by
  exact sum_extend e he (fun (i : Fin N) (t : ℝ) => (t • A i : H d)) base y

lemma penalty_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) :
    (∑ i,psi (extend e base y i))=∑ j,psi (y j) := by
  rw [sum_extend e he (fun _ t => psi t) base y]
  have hz : (∑ i,(lookup e i).elim (psi (base i)) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => exact psi_endpoint (hb i hi)
    | some j => rfl
  rw [hz,zero_add]

lemma eta_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (c : ℝ) :
    eta c A (extend e base y)=eta c (fun j => A (e j)) y := by
  apply ContinuousLinearMap.ext
  intro Z
  rw [eta_apply,eta_apply]
  have hsum := sum_extend e he (fun (i : Fin N) (t : ℝ) => ((c*psi t) • sandwich (A i) Z : H d)) base y
  rw [hsum]
  have hz : (∑ i,(lookup e i).elim ((c*psi (base i)) • sandwich (A i) Z) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => simp only [Option.elim_none,psi_endpoint (hb i hi),mul_zero,zero_smul]
    | some j => rfl
  rw [hz,zero_add]

lemma potential_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (ε lam : ℝ) :
    value ε (S A (extend e base y)) (eta 384 A (extend e base y))+
      lam*∑ i,psi (extend e base y i)=
    value ε (fixedPart e base A+S (fun j => A (e j)) y) (eta 384 (fun j => A (e j)) y)+
      lam*∑ j,psi (y j) := by
  rw [S_extend e he,eta_extend e he base A hb,penalty_extend e he base hb]

end CurrentKS.RationalFace

namespace CurrentKS.RationalSDP
open CurrentKS.RationalFace

variable {d N n : ℕ}

open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

lemma faceQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (y : Fin (activeIndices base).length → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam)
    (he : 0<error) (he1 : error≤1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i|≤1) (hy : ∀ j,|y j|≤1) :
    |(faceQuery coords base y ν lam error:ℝ)-
      (value ((ν:ℝ)/d)
        (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords)+
          S (fun j => rationalAtoms coords (activeIndex base j)) (fun j => (y j:ℝ)))
        (eta 384 (fun j => rationalAtoms coords (activeIndex base j)) (fun j => (y j:ℝ)))+
        (lam:ℝ)*∑ j,psi (y j:ℝ))|≤(error:ℝ) := by
  have hcube : Cube (fun i => ((extend (activeIndex base) base y i : ℚ):ℝ)) := by
    intro i
    change |((extend (activeIndex base) base y i : ℚ):ℝ)| ≤ 1
    exact_mod_cast extend_cube (e := activeIndex base) base y hb hy i
  have hq := potentialQuery_correct coords (extend (activeIndex base) base y)
    hA htr hν hν1 hlam he he1 hvar hcube
  have heq := potential_extend (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) (real_active_outside_endpoint base hb)
    (fun j => (y j:ℝ)) ((ν:ℝ)/d) (lam:ℝ)
  have hext := map_extend (fun q : ℚ => (q:ℝ)) (activeIndex base) base y
  have hext' : ∀ i, ((extend (activeIndex base) base y i : ℚ):ℝ) =
      extend (activeIndex base) (fun i => (base i:ℝ)) (fun j => (y j:ℝ)) i :=
    fun i => congrFun hext i
  simp_rw [hext'] at hq
  rw [heq] at hq
  exact hq

end CurrentKS.RationalSDP

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

lemma epsilon_spec [NeZero d] {ν : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < ν/(d:ℚ) ∧ ν/(d:ℚ) ≤ 1 ∧ ν/(d:ℚ)*(d:ℚ) ≤ 1 := by
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  refine ⟨div_pos hν hd,(div_le_one hd).mpr (hν1.trans hd1),?_⟩
  simpa only [div_mul_cancel₀ _ hd.ne'] using hν1

lemma activeQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (y : Fin (activeIndices base).length → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (he : 0 < error) (he1 : error ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hy : ∀ j,|y j| ≤ 1) :
    |(faceQuery coords base y ν lam error:ℝ)-activePotential coords base ν lam (pointCast y)| ≤ (error:ℝ) := by
  have hh := faceQuery_correct coords base y hA htr hν hν1 hlam he he1 hvar hb hy
  simp only [activePotential,facePotential,penalty,pointCast,Rat.cast_div,Rat.cast_natCast]
  exact hh

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma stencil_error_bounds {n : ℕ} (hn : 0 < n) {a h : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    0 < a*h^2/(128*n) ∧ a*h^2/(128*n) ≤ 1 := by
  have hn0 : (0:ℚ) < n := by exact_mod_cast hn
  have hn1 : (1:ℚ) ≤ n := by exact_mod_cast hn
  refine ⟨by positivity,(div_le_one (by positivity)).mpr ?_⟩
  have hh2 : h^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg h)
  nlinarith

lemma selection_error_bounds {a s : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1/4) :
    0 < a*s^2/4 ∧ a*s^2/4 ≤ 1 := by
  refine ⟨by positivity,(div_le_one (by norm_num : (0:ℚ) < 4)).mpr ?_⟩
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg s)
  nlinarith

lemma parameters_valid {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (parameters d n ν lam).Valid n := by
  have hd0 : (0:ℚ) < d := by exact_mod_cast hd
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hep : 0 < ν/(d:ℚ) := div_pos hν hd0
  have hep1 : ν/(d:ℚ) ≤ 1 := (div_le_one hd0).mpr (hν1.trans hd1)
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have ha1 := threshold_le_one n (ν/(d:ℚ)) hlam1
  have hM := curveBudget_one_le d n hep hσ lam
  have hMp : 0 < curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam := lt_of_lt_of_le (by norm_num) hM
  have hs := stepSize_spec ha hMp hσ
  have hh := stencilSize_spec hn ha hMp hσ
  have hρ := meshSize_spec hn ha hMp hs.1
  have he := stencil_error_bounds hn ha ha1 hh.1 hh.2.2.1
  have hg := selection_error_bounds ha ha1 hs.1 hs.2.2.1
  exact ⟨hep,hep1,hσ,ha,ha1,hM,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,hρ.1,hρ.2,schedule_radius hn ha hMp hσ,
    he.1,he.2,hg.1,hg.2⟩

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FaceStencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

lemma faceCandidates_cube [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    ∀ y∈faceCandidates coords base ν lam, ∀ i,|y i| ≤ 1 := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  exact allCandidates_cube _ _ _ _ _ _ _ p.σ hp.threshold_pos hp.threshold_le
    hp.bound_one hp.step_pos.le hp.mesh_pos hp.mesh_error
    (by linarith [hp.step_strip,hp.strip_pos]) hp.strip_pos.le hx

theorem faceChoice_spec [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    (∀ i,|faceChoice coords base ν lam i| ≤ 1) ∧
      activePotential coords base ν lam (pointCast (faceChoice coords base ν lam)) ≤
        activePotential coords base ν lam (pointCast (faceState base))-
          3*((p.a:ℝ)*(p.s:ℝ)^2)/2 := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  have hcube : ∀ y∈faceState base::faceCandidates coords base ν lam,∀ i,|y i| ≤ 1 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · exact fun i => hb (activeIndex base i)
    · exact faceCandidates_cube coords base hν hν1 hlam hlam1 hx y hy
  have herr : ∀ y∈faceState base::faceCandidates coords base ν lam,
      |(faceScore coords base ν lam y:ℝ)-activePotential coords base ν lam (pointCast y)| ≤
        ((p.a:ℝ)*(p.s:ℝ)^2)/4 := by
    intro y hy
    have hq := activeQuery_correct coords base y hA htr hν hν1 hlam.le
      hp.selectionError_pos hp.selectionError_le hvar hb (hcube y hy)
    apply hq.trans_eq
    simp only [p,parameters,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat]
  have hprog := faceCandidates_progress coords base hA hA0 hrank htr hν hν1 hlam hlam1 hvar hb hx
  refine ⟨hcube _ (select_mem _ _ _),?_⟩
  apply select_decrease (fun y => activePotential coords base ν lam (pointCast y))
    (faceScore coords base ν lam) (faceState base) (faceState base) _ herr
  obtain ⟨y,hy,hd⟩ := hprog
  refine ⟨y,List.mem_cons_of_mem _ hy,?_⟩
  nlinarith

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_MinList
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Descent

lemma minList_pos (l : List ℚ) (h : ∀ a∈l,0<a) : 0 < minList l := by
  induction l with
  | nil => norm_num [minList]
  | cons a as ih =>
    exact lt_min (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

lemma minList_le {l : List ℚ} {a : ℚ} (ha : a∈l) : minList l≤a := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ha)

end CurrentKS.Descent

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_NearestEndpoint
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N : ℕ}

lemma nearestEndpoint_abs (r : ℚ) : |nearestEndpoint r|=1 := by
  unfold nearestEndpoint
  split <;> norm_num

lemma nearestEndpoint_dist {r : ℚ} (hr : |r|≤1) : |nearestEndpoint r-r|=1-|r| := by
  unfold nearestEndpoint
  split
  · rename_i h
    rw [abs_of_nonneg h,abs_of_nonneg (by linarith [(abs_le.mp hr).2])]
  · rename_i h
    have hn : r≤0 := (lt_of_not_ge h).le
    rw [abs_of_nonpos hn,abs_of_nonpos (by linarith [(abs_le.mp hr).1])]
    ring

lemma freezeOne_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    ∀ j,|freezeOne σ x i j|≤1 := by
  unfold freezeOne
  split
  · intro j
    by_cases hj : j=i
    · subst j;simpa using (nearestEndpoint_abs (x i)).le
    · simpa only [Function.update_of_ne hj] using hx j
  · exact hx

lemma freezeOne_other (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N) (hji : j≠i) :
    freezeOne σ x i j=x j := by
  unfold freezeOne
  split <;> simp [Function.update_of_ne hji]

lemma freezeOne_assigned (σ : ℚ) (x : Fin N → ℚ) (i : Fin N) :
    |freezeOne σ x i i|=1 ∨ σ<1-|freezeOne σ x i i| := by
  unfold freezeOne
  split
  · exact Or.inl (by simpa using nearestEndpoint_abs (x i))
  · exact Or.inr (lt_of_not_ge ‹¬1-|x i|≤σ›)

lemma freezeOne_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (i j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeOne σ x i j|=1 ∨ σ<1-|freezeOne σ x i j| := by
  by_cases hji : j=i
  · subst j;exact freezeOne_assigned σ x i
  · simpa only [freezeOne_other σ x i j hji] using h

lemma freezeList_cube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    ∀ j,|freezeList σ x l j|≤1 := by
  induction l generalizing x with
  | nil => exact hx
  | cons i is ih => exact ih _ (freezeOne_cube σ x hx i)

lemma freezeList_preserves_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N)
    (h : |x j|=1 ∨ σ<1-|x j|) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => exact h
  | cons i is ih => exact ih _ (freezeOne_preserves_assigned σ x i j h)

lemma freezeList_assigned (σ : ℚ) (x : Fin N → ℚ) (l : List (Fin N)) (j : Fin N) (hj : j∈l) :
    |freezeList σ x l j|=1 ∨ σ<1-|freezeList σ x l j| := by
  induction l generalizing x with
  | nil => simp at hj
  | cons i is ih =>
    rcases List.mem_cons.mp hj with hij|hj
    · subst j
      exact freezeList_preserves_assigned σ _ is i (freezeOne_assigned σ x i)
    · exact ih _ hj

lemma freezeAll_strip (σ : ℚ) (x : Fin N → ℚ) (j : Fin N)
    (hj : |freezeAll σ x j|<1) : |freezeAll σ x j|<1-σ := by
  have hh := freezeList_assigned σ x (List.finRange N) j (List.mem_finRange j)
  change |freezeAll σ x j|=1 ∨ σ<1-|freezeAll σ x j| at hh
  rcases hh with h|h <;> linarith

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ShiftFeasibleMap
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma shift_feasible_of_map_le (S T : H d) (η θ : H d →L[ℝ] H d)
    {r : ℝ} (hplus : T-S ≤ r • (Hermitian.one : H d))
    (hminus : S-T ≤ r • (Hermitian.one : H d))
    (hle : ∀ X ∈ psdCone d, θ X ≤ η X) (z : Point d) (hz : z ∈ feasible S η) :
    (z.1+r,z.2) ∈ feasible T θ := by
  rw [feasible_iff] at hz ⊢
  refine ⟨hz.1,hz.2.1,?_,?_⟩
  · have h := add_le_add hz.2.2.1 hplus
    have he : invH z.2.1+T+θ z.2.2 ≤ invH z.2.1+S+η z.2.2+(T-S) := by
      have hh := add_le_add_left (hle z.2.2 (show z.2.2 ∈ psdCone d from hz.2.1.posSemidef)) (invH z.2.1+T)
      convert hh using 1 <;> first | rfl | abel
    convert he.trans h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | module
  · have h := add_le_add hz.2.2.2 hminus
    have he : invH z.2.2-T+θ z.2.1 ≤ invH z.2.2-S+η z.2.1+(S-T) := by
      have hh := add_le_add_left (hle z.2.1 (show z.2.1 ∈ psdCone d from hz.1.posSemidef)) (invH z.2.2-T)
      convert hh using 1 <;> first | rfl | abel
    convert he.trans h using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | module

end CurrentKS.Variational

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma endpoint_eta_le {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) (x : Coordinates N)
    (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t|=1) :
    ∀ X ∈ psdCone d,eta c A (Function.update x i t) X ≤ eta c A x X := by
  intro X hX
  rw [eta_update,psi_endpoint ht]
  have hs : (c*(0-psi (x i))) • sandwich (A i) X ≤ 0 := by
    simpa only [zero_smul] using scalar_mono_psd (sandwich_psd (A i) X hX)
      (show c*(0-psi (x i)) ≤ 0 by nlinarith [(psi_bounds (hx i)).1])
  simpa only [zero_add,add_comm] using add_le_add_left hs (eta c A x X)

lemma negative_le_operatorNorm (A : H d) : -A ≤ operatorNorm A • (Hermitian.one : H d) := by
  have h := le_operatorNorm_smul_one (-A)
  have he : operatorNorm (-A) = operatorNorm A := by
    rw [← neg_one_smul ℝ A,operatorNorm_smul]
    norm_num
  rwa [he] at h

lemma endpoint_value_shift [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    value ε (S A (Function.update x i t)) (eta c A (Function.update x i t)) ≤
      value ε (S A x) (eta c A x)+|t-x i| *operatorNorm (A i) := by
  let D := (t-x i) • A i
  have hd : S A (Function.update x i t)-S A x = D := by rw [S_update]; abel
  have hm : S A x-S A (Function.update x i t) = -D := by rw [S_update]; abel
  have hp : S A (Function.update x i t)-S A x ≤ operatorNorm D • (Hermitian.one : H d) := by
    rw [hd]; exact le_operatorNorm_smul_one D
  have hn : S A x-S A (Function.update x i t) ≤ operatorNorm D • (Hermitian.one : H d) := by
    rw [hm]; exact negative_le_operatorNorm D
  have hf := shift_feasible_of_map_le _ _ _ _ hp hn (endpoint_eta_le hc A x hx i ht) z hz
  have hv := value_le_feasible ε hε _ _ (eta_positive hc A (Cube_update hx i ht.le)) _ hf
  rw [value_eq_of_min ε _ _ z hz hmin]
  calc
    _ ≤ objective ε (z.1+operatorNorm D,z.2) := hv
    _ = objective ε z+|t-x i| *operatorNorm (A i) := by
      dsimp [objective,D]
      rw [operatorNorm_smul]
      ring

lemma endpoint_shift_potential [NeZero d] {c ε lam : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : Fin N → H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    potential c ε lam A (Function.update x i t) ≤
      potential c ε lam A x+|t-x i| *operatorNorm (A i)-lam*psi (x i) := by
  have hv := endpoint_value_shift hc hε A x hx i ht z hz hmin
  rw [potential,potential,sum_update_composite (fun (_ : Fin N) (r : ℝ) => psi r) x i t,
    psi_endpoint ht,add_zero]
  nlinarith

lemma psi_sq_ge_distance {x : ℝ} (hx : |x| ≤ 1) : 1-|x| ≤ psi x^2 := by
  rcases lt_or_eq_of_le hx with hi|he
  · have hp := psi_pos hi
    have hc := psi_cube hi
    have h1 := psi_le_one hi
    have ha := abs_nonneg x
    have hr := sq_abs x
    have hprod := mul_nonneg (sq_nonneg (psi x)) (sub_nonneg.mpr h1)
    have hdist := mul_nonneg ha (sub_nonneg.mpr hx)
    nlinarith
  · rw [psi_endpoint he,he]; norm_num

lemma freeze_scalar {x lam ν : ℝ} (hx : |x| ≤ 1) (hlam : 0 ≤ lam) (hν : 0 < ν)
    (hclose : 1-|x| ≤ lam^2/ν) :
    (1-|x|)*Real.sqrt ν ≤ lam*psi x := by
  have hz : 0 ≤ 1-|x| := sub_nonneg.mpr hx
  have hv := Real.sq_sqrt hν.le
  have hr := Real.sq_sqrt hz
  have hab := (le_div_iff₀ hν).mp hclose
  have hp := (psi_bounds hx).1
  have hsp : Real.sqrt (1-|x|) ≤ psi x := by
    nlinarith [psi_sq_ge_distance hx,Real.sqrt_nonneg (1-|x|)]
  have hroot : Real.sqrt (1-|x|)*Real.sqrt ν ≤ lam := by
    have hs : (Real.sqrt (1-|x|)*Real.sqrt ν)^2 ≤ lam^2 := by
      rw [mul_pow,hr,hv];exact hab
    nlinarith [Real.sqrt_nonneg ν,Real.sqrt_nonneg (1-|x|)]
  have hh := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (1-|x|))
  have hh' : (1-|x|)*Real.sqrt ν ≤ lam*Real.sqrt (1-|x|) := by
    calc
      (1-|x|)*Real.sqrt ν = Real.sqrt (1-|x|)*(Real.sqrt (1-|x|)*Real.sqrt ν) := by rw [← mul_assoc,← sq,hr]
      _ ≤ Real.sqrt (1-|x|)*lam := hh
      _ = lam*Real.sqrt (1-|x|) := mul_comm _ _
  exact hh'.trans (mul_le_mul_of_nonneg_left hsp hlam)

theorem freeze_potential [NeZero d] {c ε lam ν : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hlam : 0 ≤ lam) (hν : 0 < ν) (A : Fin N → H d) (x : Coordinates N)
    (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t|=1) (hne : |t-x i|=1-|x i|)
    (hAn : operatorNorm (A i) ≤ Real.sqrt ν) (hclose : 1-|x i| ≤ lam^2/ν)
    (z : Point d) (hz : z ∈ feasible (S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S A x) (eta c A x),objective ε z ≤ objective ε w) :
    potential c ε lam A (Function.update x i t) ≤ potential c ε lam A x := by
  have he := endpoint_shift_potential hc hε A x hx i ht z hz hmin (lam:=lam)
  rw [hne] at he
  have hh := mul_le_mul_of_nonneg_left hAn (sub_nonneg.mpr (hx i))
  have hs := freeze_scalar (hx i) hlam hν hclose
  linarith

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FreezePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma freezeOne_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ν lam ε : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam) (hε : 0<ε) (hεd : ε*d≤1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N) :
    potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (freezeOne (lam^2/ν) x i j:ℝ))≤
      potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (x j:ℝ)) := by
  unfold freezeOne
  split
  · rename_i hclose
    let xr : Coordinates N := fun j => (x j:ℝ)
    have hxr : Cube xr := fun j => by
      change |(x j:ℝ)| ≤ 1
      exact_mod_cast hx j
    have hord := S_bounds A hA htr hxr
    have ηbound := eta_one_bound (by norm_num : (0:ℝ)≤384) A hvar hxr
    have ηbound' : eta 384 A xr (Hermitian.one : H d)≤(384:ℝ) • (Hermitian.one : H d) := by
      apply ηbound.trans
      exact scalar_mono_psd one_mem_psdCone (by exact_mod_cast (show 384*ν≤(384:ℚ) by linarith))
    obtain ⟨z,hz,_,hmin⟩ := normalized_minimizer (ε:=(ε:ℝ)) (S A xr) (eta 384 A xr)
      (eta_positive (by norm_num : (0:ℝ)≤384) A hxr) (by exact_mod_cast hε)
      (by exact_mod_cast hεd) hord.1 hord.2 ηbound'
    have ht : |(nearestEndpoint (x i):ℝ)|=1 := by exact_mod_cast nearestEndpoint_abs (x i)
    have hdist : |(nearestEndpoint (x i):ℝ)-xr i|=1-|xr i| := by
      change |(nearestEndpoint (x i):ℝ)-(x i:ℝ)|=1-|(x i:ℝ)|
      exact_mod_cast nearestEndpoint_dist (hx i)
    have hh := freeze_potential (by norm_num : (0:ℝ)≤384) (ε:=(ε:ℝ)) (lam:=(lam:ℝ)) (ν:=(ν:ℝ))
      (by exact_mod_cast hε.le) (by exact_mod_cast hlam) (by exact_mod_cast hν) A xr hxr i ht hdist
      (atom_operatorNorm_le_sqrt A (by exact_mod_cast hν.le) hvar i)
      (by change 1-|(x i:ℝ)| ≤ (lam:ℝ)^2/(ν:ℝ); exact_mod_cast hclose) z hz hmin
    have heq : (fun j => (Function.update x i (nearestEndpoint (x i)) j : ℝ)) =
        Function.update xr i (nearestEndpoint (x i) : ℝ) := by
      ext j
      by_cases hji : j=i
      · subst j;simp
      · simp [Function.update_of_ne hji,xr]
    simpa only [heq] using hh
  · exact le_refl _

lemma freezeList_potential [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    {ν lam ε : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam) (hε : 0<ε) (hεd : ε*d≤1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (l : List (Fin N)) :
    potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (freezeList (lam^2/ν) x l j:ℝ))≤
      potential 384 (ε:ℝ) (lam:ℝ) A (fun j => (x j:ℝ)) := by
  induction l generalizing x with
  | nil => exact le_refl _
  | cons i is ih =>
    exact (ih _ (freezeOne_cube _ _ hx i)).trans
      (freezeOne_potential A hA htr hν hν1 hlam hε hεd hvar x hx i)

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Transition
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

lemma freezeAll_stripCube (σ : ℚ) (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    StripCube σ (freezeAll σ x) :=
  ⟨freezeList_cube σ x hx _,fun i hi => (freezeAll_strip σ x i hi).le⟩

lemma StripCube.faceState {σ : ℚ} {x : Fin N → ℚ} (hx : StripCube σ x) :
    ∀ i,|faceState x i| ≤ 1-σ :=
  fun i => hx.2 (activeIndex x i) (activeIndex_interior x i)

lemma uniformDrop_pos [NeZero d] {ν lam : ℚ} (hν : 0 < ν) (hlam : 0 < lam) :
    0 < uniformDrop d N ν lam := by
  apply minList_pos
  intro q hq
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp hq
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d:ℚ) := div_pos hν hd
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have hM := curveBudget_one_le d n hε hσ lam
  have hs := stepSize_spec ha (lt_of_lt_of_le (by norm_num : (0:ℚ)<1) hM) hσ
  change 0 < threshold n (ν/(d:ℚ)) lam*(stepSize _ _ _)^2
  exact mul_pos ha (sq_pos_of_pos hs.1)

lemma uniformDrop_le (d N n : ℕ) (ν lam : ℚ) (hn : n ≤ N) :
    uniformDrop d N ν lam ≤ (parameters d n ν lam).a*(parameters d n ν lam).s^2 := by
  apply minList_le
  apply List.mem_map.mpr
  exact ⟨n,List.mem_range.mpr (by omega),rfl⟩

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

lemma fullPotential_extend (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) (hb : ∀ i,|base i| ≤ 1) (y : Fin (activeIndices base).length → ℚ) :
    fullPotential coords ν lam (extend (activeIndex base) base y)=
      activePotential coords base ν lam (pointCast y) := by
  have he := potential_extend (activeIndex base) (activeIndex_injective base)
    (pointCast base) (rationalAtoms coords) (real_active_outside_endpoint base hb)
    (pointCast y) ((ν/(d:ℚ):ℚ):ℝ) (lam:ℝ)
  have hc := map_extend (fun q : ℚ => (q:ℝ)) (activeIndex base) base y
  change pointCast (extend (activeIndex base) base y)=extend (activeIndex base) (pointCast base) (pointCast y) at hc
  unfold fullPotential potential
  rw [hc]
  exact he

lemma fullPotential_self (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (ν lam : ℚ) (hb : ∀ i,|base i| ≤ 1) :
    activePotential coords base ν lam (pointCast (faceState base))=fullPotential coords ν lam base := by
  have hh := fullPotential_extend coords base ν lam hb (faceState base)
  change fullPotential coords ν lam (extend (activeIndex base) base (fun j => base (activeIndex base j)))=_ at hh
  rw [extend_self] at hh
  exact hh.symm

lemma fullPotential_freeze [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (x : Fin N → ℚ) (hx : ∀ i,|x i| ≤ 1) :
    fullPotential coords ν lam (freezeAll (lam^2/ν) x) ≤ fullPotential coords ν lam x := by
  have hep := epsilon_spec (d:=d) hν hν1
  exact freezeList_potential (rationalAtoms coords) hA htr hν hν1 hlam hep.1 hep.2.2 hvar x hx _

theorem transition_spec_oai [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (x y : Fin N → ℚ) (hx : StripCube (lam^2/ν) x)
    (hs : transition coords ν lam x=some y) :
    StripCube (lam^2/ν) y ∧
      fullPotential coords ν lam y ≤ fullPotential coords ν lam x-(uniformDrop d N ν lam:ℝ) := by
  by_cases hn : (activeIndices x).length=0
  · simp [transition,hn] at hs
  · let : NeZero (activeIndices x).length := ⟨hn⟩
    have hchoice := faceChoice_spec coords x hA hA0 hrank htr hν hν1 hlam hlam1 hvar hx.1 hx.faceState
    let z := extend (activeIndex x) x (faceChoice coords x ν lam)
    have he : y=freezeAll (lam^2/ν) z := by
      simpa only [transition,dite_eq_right hn,Option.some.injEq] using hs.symm
    subst y
    have hz : ∀ i,|z i| ≤ 1 := extend_cube x _ hx.1 hchoice.1
    refine ⟨freezeAll_stripCube _ z hz,?_⟩
    have hf := fullPotential_freeze coords hA htr hν hν1 hlam.le hvar z hz
    have hc : fullPotential coords ν lam z ≤ fullPotential coords ν lam x-
        3*((parameters d (activeIndices x).length ν lam).a:ℝ)*
          ((parameters d (activeIndices x).length ν lam).s:ℝ)^2/2 := by
      rw [fullPotential_extend coords x ν lam hx.1]
      simpa only [fullPotential_self coords x ν lam hx.1,mul_assoc] using hchoice.2
    have hd : (uniformDrop d N ν lam:ℝ) ≤
        ((parameters d (activeIndices x).length ν lam).a:ℝ)*
          ((parameters d (activeIndices x).length ν lam).s:ℝ)^2 := by
      exact_mod_cast uniformDrop_le d N (activeIndices x).length ν lam (activeIndices_length_le x)
    have hdp : (0:ℝ) < uniformDrop d N ν lam := by exact_mod_cast uniformDrop_pos hν hlam
    linarith

end
end CurrentKS.RationalFace

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.RationalFace.transition_spec_oai := @OAI.CurrentKS.RationalFace.transition_spec_oai
