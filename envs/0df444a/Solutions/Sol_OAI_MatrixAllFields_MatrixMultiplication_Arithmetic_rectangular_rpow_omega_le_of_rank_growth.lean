-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:45.150686+00:00
-- url     : https://prove2.me/submissions/d2155920-5862-4ce0-b7ab-218642036f89

import Mathlib
import Definitions.Def_MatrixFields
import Definitions.Def_OAIQ254M003

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ArithmeticComplexity
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k := by
  constructor
  · intro h A B i k
    exact congrFun (congrFun (h A B) i) k
  · intro h A B
    funext i k
    exact h A B i k

end MatrixAlgorithm

theorem scalarAlgorithm_correct (F : Type*) [Field F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

theorem one_le_innerSize {n : ℕ} (hn : 1 ≤ n) (k : ℝ) : 1 ≤ innerSize n k := by
  apply Nat.one_le_ceil_iff.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)) k

theorem innerSize_le_pow {a b n t : ℕ} {k : ℝ} (hk : 0 ≤ k)
    (hn : n ≤ a ^ t) (hab : (a : ℝ) ^ k ≤ b) : innerSize n k ≤ b ^ t := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ k ≤ ((a ^ t : ℕ) : ℝ) ^ k :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hk
    _ = ((a : ℝ) ^ k) ^ t := by
      rw [Nat.cast_pow, ← Real.rpow_pow_comm (Nat.cast_nonneg a)]
    _ ≤ (b : ℝ) ^ t := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
    _ = ((b ^ t : ℕ) : ℝ) := by rw [Nat.cast_pow]

end MatrixMultiplication.Arithmetic

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_TerminalRelabel
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

theorem contract_matrixCoefficients [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (left : A × B → K) (right : B × C → K) (i : A) (k : C) :
    contract (matrixCoefficients A B C) left right (k, i) =
      ∑ j, left (i, j) * right (j, k) := by
  simp [contract, matrixCoefficients, Fintype.sum_prod_type, ite_and, ite_mul]

end Tensor






end MatrixMultiplication.Foundation

end




end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_RecursiveBlockPrograms
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section




noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem sum_fin_castLE_of_zero {n m : ℕ} (h : n ≤ m) (f : Fin m → F)
    (hf : ∀ j : Fin m, n ≤ j.val → f j = 0) :
    (∑ j : Fin m, f j) = ∑ j : Fin n, f (Fin.castLE h j) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) ?_
    (fun j : Fin n => f (Fin.castLE h j)) f ?_ (fun _ => rfl)
  · intro i j hij
    exact Fin.ext (congrArg (fun v : Fin m => v.val) hij)
  · intro j hj
    exact hf j (le_of_not_gt fun hsmall => hj ⟨⟨j.val, hsmall⟩, Fin.ext rfl⟩)

theorem zeroPadMatrix_mul {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F)
    (i : Fin a) (k : Fin c) :
    (zeroPadMatrix A B M * zeroPadMatrix B C N) (Fin.castLE ha i) (Fin.castLE hc k) =
      (M * N) i k := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc
    (∑ j : Fin B,
        zeroPadMatrix A B M (Fin.castLE ha i) j *
          zeroPadMatrix B C N j (Fin.castLE hc k)) =
        ∑ j : Fin b,
          zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) *
            zeroPadMatrix B C N (Fin.castLE hb j) (Fin.castLE hc k) := by
      apply sum_fin_castLE_of_zero hb
      intro j hj
      simp [zeroPadMatrix, not_lt_of_ge hj]
    _ = ∑ j : Fin b, M i j * N j k := by simp

theorem padSource_eval {a b c A B C : ℕ}
    (M : Matrix (Fin a) (Fin b) F) (N : Matrix (Fin b) (Fin c) F) :
    (fun x : MatrixInput A B C => Sum.elim (matrixInputs M N) id (padSource x)) =
      matrixInputs (zeroPadMatrix A B M) (zeroPadMatrix B C N) := by
  funext x
  rcases x with ⟨i, j⟩ | ⟨j, k⟩
  · by_cases hi : i.val < a <;> by_cases hj : j.val < b <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hi, hj]
  · by_cases hj : j.val < b <;> by_cases hk : k.val < c <;>
      simp [padSource, matrixInputs, zeroPadMatrix, hj, hk]

namespace MatrixAlgorithm

theorem pad_correct {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    {P : MatrixAlgorithm F A B C} (hP : P.Correct) : (pad ha hb hc P).Correct := by
  intro M N
  funext i k
  change (P.program.mapSource (padSource (a := a) (b := b) (c := c))).eval
    (matrixInputs M N) (P.output (Fin.castLE ha i) (Fin.castLE hc k)) = (M * N) i k
  rw [Program.eval_mapSource, padSource_eval]
  have hentry := congrFun (congrFun
    (hP (zeroPadMatrix A B M) (zeroPadMatrix B C N)) (Fin.castLE ha i)) (Fin.castLE hc k)
  exact hentry.trans (zeroPadMatrix_mul ha hb hc M N i k)

theorem exists_restrict {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) (hP : P.Correct) :
    ∃ Q : MatrixAlgorithm F a b c, Q.Correct ∧ Q.cost ≤ P.cost :=
  ⟨pad ha hb hc P, pad_correct ha hb hc hP, (pad_cost_eq ha hb hc P).le⟩

end MatrixAlgorithm

end MatrixMultiplication.Arithmetic







namespace MatrixMultiplication.Arithmetic.RecursiveBlock

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F]

namespace LinearExpression

variable {Input : Type*}

theorem eval_sumFin (n : ℕ) (f : Fin n → Expression F Input) (inputs : Input → F) :
    (sumFin n f).eval inputs = ∑ i, (f i).eval inputs := by
  induction n with
  | zero => simp [sumFin, Expression.eval]
  | succ n ih =>
    simp only [sumFin, Expression.eval, ih, Fin.sum_univ_succ]

theorem cost_sumFin (n : ℕ) (f : Fin n → Expression F Input) :
    (sumFin n f).cost = (∑ i, (f i).cost) + n := by
  induction n with
  | zero => simp [sumFin, Expression.cost]
  | succ n ih =>
    simp only [sumFin, Expression.cost, ih, Fin.sum_univ_succ]
    omega

theorem eval_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → Input) (inputs : Input → F) :
    (linear a wire).eval inputs = ∑ i, a i * inputs (wire i) := by
  rw [linear, eval_sumFin]
  exact (Fintype.equivFin Term).symm.sum_comp (fun i => a i * inputs (wire i))

theorem cost_linear {Term : Type*} [Fintype Term]
    (a : Term → F) (wire : Term → Input) :
    (linear a wire).cost = 2 * Fintype.card Term := by
  simp [linear, cost_sumFin, Expression.cost, two_mul]

end LinearExpression

namespace Family

variable {Input Mid Output : Type*}

theorem eval_expressions [Fintype Output] (e : Output → Expression F Input)
    (inputs : Input → F) (o : Output) :
    (expressions e).eval inputs o = (e o).eval inputs :=
  (Expression.compileFamily e).correct inputs o

theorem cost_expressions [Fintype Output] (e : Output → Expression F Input) :
    (expressions e).cost = ∑ o, (e o).cost :=
  (Expression.compileFamily e).cost_eq

theorem eval_compose (p : Family F Input Mid) (q : Family F Mid Output)
    (inputs : Input → F) (o : Output) :
    (compose p q).eval inputs o = q.eval (p.eval inputs) o :=
  (p.program.substitute q.program p.output).correct inputs (q.output o)

theorem cost_compose (p : Family F Input Mid) (q : Family F Mid Output) :
    (compose p q).cost = p.cost + q.cost :=
  (p.program.substitute q.program p.output).cost_eq

theorem eval_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family F Input Output) (inputs : NewInput → F) (o : Output) :
    (p.mapInputs f).eval inputs o = p.eval (fun i => inputs (f i)) o := by
  exact Program.eval_mapInput f p.program inputs (p.output o)

omit [Field F] in
theorem cost_mapInputs {NewInput : Type*} (f : Input → NewInput)
    (p : Family F Input Output) : (p.mapInputs f).cost = p.cost := by
  exact Program.cost_mapInput f p.program

theorem eval_parallel (r : ℕ) (p : Fin r → Family F Input Output)
    (inputs : Input → F) (o : Fin r × Output) :
    (parallel r p).eval inputs o = (p o.1).eval inputs o.2 := by
  induction r with
  | zero => exact Fin.elim0 o.1
  | succ r ih =>
    rcases o with ⟨i, o⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Program.eval_append_old _ _ inputs _
    · exact (Program.eval_append_new _ _ inputs _).trans
        (ih (fun j => p j.succ) (j, o))

omit [Field F] in
theorem cost_parallel (r : ℕ) (p : Fin r → Family F Input Output) :
    (parallel r p).cost = ∑ i, (p i).cost := by
  induction r with
  | zero => simp [parallel, cost, Program.cost]
  | succ r ih =>
    change ((p 0).program.append (parallel r (fun i => p i.succ)).program).cost = _
    rw [Program.cost_append]
    change (p 0).cost + (parallel r (fun i => p i.succ)).cost = _
    rw [ih, Fin.sum_univ_succ]

theorem eval_copies (r : ℕ) (p : Family F Input Output)
    (inputs : Fin r × Input → F) (o : Fin r × Output) :
    (copies r p).eval inputs o = p.eval (fun x => inputs (o.1, x)) o.2 := by
  rw [copies, eval_parallel, eval_mapInputs]

omit [Field F] in
theorem cost_copies (r : ℕ) (p : Family F Input Output) :
    (copies r p).cost = r * p.cost := by
  simp [copies, cost_parallel, cost_mapInputs]

theorem eval_ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) (hp : p.Correct)
    (inputs : MatrixInput m l q → F) (o : Fin m × Fin q) :
    (ofMatrix p).eval inputs o =
      ∑ j, inputs (.inl (o.1, j)) * inputs (.inr (j, o.2)) := by
  have h := (MatrixAlgorithm.correct_iff_entries p).mp hp
    (fun i j => inputs (.inl (i, j))) (fun j k => inputs (.inr (j, k))) o.1 o.2
  have hi : matrixInputs (fun i j => inputs (.inl (i, j)))
      (fun j k => inputs (.inr (j, k))) = inputs := by
    funext x
    cases x <;> rfl
  rw [hi] at h
  exact h

end Family

section BlockIdentities

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

theorem rank_bilinear_identity
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (left : Fin n₁ × Fin n₂ → F) (right : Fin n₂ × Fin n₃ → F)
    (i : Fin n₁) (k : Fin n₃) :
    (∑ q, c q (k, i) * (∑ x, a q x * left x) * (∑ y, b q y * right y)) =
      ∑ j, left (i, j) * right (j, k) := by
  rw [← Tensor.contract_matrixCoefficients left right i k]
  rw [h]
  simp only [Tensor.contract, Tensor.rankOne, Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ q, ∑ y, ∑ x, c q (k, i) * (a q x * left x) * (b q y * right y)) =
        ∑ q, ∑ x, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.sum_comm
    _ = ∑ x, ∑ q, ∑ y, c q (k, i) * (a q x * left x) * (b q y * right y) :=
      Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ q, a q x * b q y * c q (k, i) * left x * right y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem block_identity
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (∑ q, c q (k, i) * ((leftBlock a A q) * (rightBlock b B q)) s u) =
      (A * B) (join i s) (join k u) := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlocal (t : Fin m₂) := rank_bilinear_identity a b c h
    (fun x => A (join x.1 s) (join x.2 t))
    (fun y => B (join y.1 t) (join y.2 u)) i k
  simp only [leftBlock, rightBlock]
  simp_rw [← mul_assoc, hlocal]
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type _).symm.trans
    (finProdFinEquiv.sum_comp (fun j => A (join i s) j * B j (join k u)))

end BlockIdentities

section BlockPrograms

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

theorem inputFamily_eval (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (q : Fin r) (x : MatrixInput m₁ m₂ m₃) :
    (inputFamily a b).eval (matrixInputs A B) (q, x) =
      matrixInputs (leftBlock a A q) (rightBlock b B q) x := by
  cases x with
  | inl x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, leftBlock]
  | inr x =>
    simp only [inputFamily, Family.eval_expressions, inputExpressions,
      LinearExpression.eval_linear, matrixInputs, rightBlock]

theorem inputFamily_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    (inputFamily (m₁ := m₁) (m₂ := m₂) (m₃ := m₃) a b).cost =
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃) := by
  rw [inputFamily, Family.cost_expressions]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type,
    inputExpressions, LinearExpression.cost_linear, Fintype.card_prod,
    Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

theorem recursiveProducts_eval (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F)
    (q : Fin r) (s : Fin m₁) (u : Fin m₃) :
    (recursiveProducts a b p).eval (matrixInputs A B) (q, (s, u)) =
      ((leftBlock a A q) * (rightBlock b B q)) s u := by
  rw [recursiveProducts, Family.eval_compose, Family.eval_copies,
    Family.eval_ofMatrix _ hp]
  simp only [inputFamily_eval, matrixInputs, Matrix.mul_apply]

theorem recursiveProducts_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (p : MatrixAlgorithm F m₁ m₂ m₃) :
    (recursiveProducts a b p).cost =
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃) + r * p.cost := by
  rw [recursiveProducts, Family.cost_compose, inputFamily_cost,
    Family.cost_copies, Family.cost_ofMatrix]

theorem outputFamily_eval (c : Fin r → Fin n₃ × Fin n₁ → F)
    (inputs : Fin r × (Fin m₁ × Fin m₃) → F)
    (i : Fin n₁) (k : Fin n₃) (s : Fin m₁) (u : Fin m₃) :
    (outputFamily c).eval inputs (join i s, join k u) =
      ∑ q, c q (k, i) * inputs (q, (s, u)) := by
  simp only [outputFamily, Family.eval_expressions, outputExpressions,
    LinearExpression.eval_linear, join, Equiv.symm_apply_apply]

theorem outputFamily_cost (c : Fin r → Fin n₃ × Fin n₁ → F) :
    (outputFamily (m₁ := m₁) (m₃ := m₃) c).cost = 2 * r * n₁ * n₃ * m₁ * m₃ := by
  simp only [outputFamily, Family.cost_expressions, outputExpressions,
    LinearExpression.cost_linear, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  ring

theorem algorithm_correct
    (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (h : Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃) =
      fun x y z => ∑ q, Tensor.rankOne (a q) (b q) (c q) x y z)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct) : (algorithm a b c p).Correct := by
  intro A B
  funext i k
  obtain ⟨⟨i, s⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨k, u⟩, rfl⟩ := finProdFinEquiv.surjective k
  change ((recursiveProducts a b p).compose (outputFamily c)).eval
    (matrixInputs A B) (join i s, join k u) = _
  rw [Family.eval_compose, outputFamily_eval]
  simp_rw [recursiveProducts_eval a b p hp A B]
  exact block_identity a b c h A B i k s u

theorem algorithm_cost (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) :
    (algorithm a b c p).cost = r * p.cost +
      2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃ + n₁ * n₃ * m₁ * m₃) := by
  change ((recursiveProducts a b p).compose (outputFamily c)).cost = _
  rw [Family.cost_compose, recursiveProducts_cost, outputFamily_cost]
  ring

theorem rank_block_step
    (h : Tensor.RankAtMost (Tensor.matrixCoefficients (K := F) (Fin n₁) (Fin n₂) (Fin n₃)) r)
    (p : MatrixAlgorithm F m₁ m₂ m₃) (hp : p.Correct) :
    ∃ q : MatrixAlgorithm F (n₁ * m₁) (n₂ * m₂) (n₃ * m₃), q.Correct ∧
      q.cost = r * p.cost +
        2 * r * (n₁ * n₂ * m₁ * m₂ + n₂ * n₃ * m₂ * m₃ + n₁ * n₃ * m₁ * m₃) := by
  rcases h with ⟨a, b, c, h⟩
  exact ⟨algorithm a b c p, algorithm_correct a b c h p hp, algorithm_cost a b c p⟩

end BlockPrograms

end MatrixMultiplication.Arithmetic.RecursiveBlock

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ArithmeticExponent
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.aPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.bPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.initialPositiveFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.activeWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.carriedWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.dueWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRegrouping.producedWordsFintype
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic
section

namespace Program

variable {F Input : Type*}

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p with
  | nil => simp [registerCost, cost]
  | step p g ih => simp [registerCost, Fin.sum_univ_succ, ih, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Field F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  revert i
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      change g.cost = 0 at hi
      cases g with
      | constant z => exact Or.inl ⟨z, fun _ => rfl⟩
      | input a => exact Or.inr ⟨a, fun _ => rfl⟩
      | add a b => simp [Gate.cost] at hi
      | sub a b => simp [Gate.cost] at hi
      | mul a b => simp [Gate.cost] at hi
    · intro hi
      simpa only [eval_step_succ] using ih j hi

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

theorem elementaryProduct (i x : Fin a) (j : Fin b) (k z : Fin c) :
    (elementaryLeft (F := F) i j * elementaryRight (F := F) j k) x z =
      if (x, z) = (i, k) then 1 else 0 := by
  by_cases hi : x = i <;> by_cases hk : z = k <;>
    simp [Matrix.mul_apply, elementaryLeft, elementaryRight, hi, hk]

end ElementaryMatrices

namespace MatrixAlgorithm

variable {F : Type*} [Field F] {a b c : ℕ}

theorem output_injective (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : Function.Injective (fun o : Fin a × Fin c => P.output o.1 o.2) := by
  classical
  intro x y hxy
  change P.output x.1 x.2 = P.output y.1 y.2 at hxy
  let j : Fin b := ⟨0, by omega⟩
  let A := elementaryLeft (F := F) x.1 j
  let B := elementaryRight (F := F) j x.2
  have hx := congrFun (congrFun (hP A B) x.1) x.2
  have hy := congrFun (congrFun (hP A B) y.1) y.2
  have heq : (A * B) x.1 x.2 = (A * B) y.1 y.2 := by
    rw [← hx, ← hy]
    change P.program.eval (matrixInputs A B) (P.output x.1 x.2) =
      P.program.eval (matrixInputs A B) (P.output y.1 y.2)
    rw [hxy]
  simp only [A, B, elementaryProduct, Prod.eta, ite_true, if_true] at heq
  by_contra hne
  have hyx : y ≠ x := Ne.symm hne
  simp [hyx] at heq

theorem one_le_output_registerCost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) (i : Fin a) (k : Fin c) :
    1 ≤ P.program.registerCost (P.output i k) := by
  by_contra hn
  have hzero : P.program.registerCost (P.output i k) = 0 := by omega
  let j : Fin b := ⟨0, by omega⟩
  have hentry (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) :
      P.program.eval (matrixInputs A B) (P.output i k) = (A * B) i k :=
    congrFun (congrFun (hP A B) i) k
  rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero
      (P.output i k) hzero with ⟨z, hz⟩ | ⟨u, hu⟩
  · have hz0 : z = 0 := by
      have h := hentry 0 0
      rw [hz] at h
      simpa using h
    have hz1 : z = 1 := by
      have h := hentry (elementaryLeft i j) (elementaryRight j k)
      rw [hz] at h
      simpa only [elementaryProduct, ite_true, if_true] using h
    exact (zero_ne_one : (0 : F) ≠ 1) (hz0.symm.trans hz1)
  · rcases u with ⟨x, y⟩ | ⟨y, z⟩
    · have h := hentry (fun _ _ => 1) 0
      rw [hu] at h
      change (1 : F) = ∑ _ : Fin b, (1 : F) * 0 at h
      simp at h
    · have h := hentry 0 (fun _ _ => 1)
      rw [hu] at h
      change (1 : F) = ∑ _ : Fin b, (0 : F) * 1 at h
      simp at h

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  classical
  let f : Fin a × Fin c → Fin P.registers := fun o => P.output o.1 o.2
  have hf : Function.Injective f := P.output_injective hb hP
  calc
    a * c = ∑ _o : Fin a × Fin c, (1 : ℕ) := by simp
    _ ≤ ∑ o : Fin a × Fin c, P.program.registerCost (f o) := by
      apply Finset.sum_le_sum
      intro o ho
      exact P.one_le_output_registerCost hb hP o.1 o.2
    _ = ∑ r ∈ Finset.univ.image f, P.program.registerCost r := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => hf h
    _ ≤ ∑ r, P.program.registerCost r :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = P.cost := P.program.sum_registerCost

end MatrixAlgorithm

theorem rectangularAdmissibleExponent_two_le {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : 2 ≤ τ := by
  by_contra hneg
  have hτlt : τ < 2 := lt_of_not_ge hneg
  let ε : ℝ := (2 - τ) / 2
  have hε : 0 < ε := by dsimp [ε] <;> linarith
  obtain ⟨C, hC, hbound⟩ := hτ ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (max (C ^ ε⁻¹) 1)
  have hnreal : 1 < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
  have hn1 : 1 ≤ n := (Nat.one_le_cast (α := ℝ)).mp hnreal.le
  have hpow : C < (n : ℝ) ^ ε :=
    (Real.rpow_inv_lt_iff_of_pos hC.le (Nat.cast_nonneg n) hε).mp
      (lt_of_le_of_lt (le_max_left _ _) hn)
  obtain ⟨P, hP, hcost⟩ := hbound n hn1
  have hlower : (n : ℝ) ^ (2 : ℕ) ≤ P.cost := by
    have h : n ^ 2 ≤ P.cost := by
      simpa [pow_two] using P.output_size_le_cost (one_le_innerSize hn1 k) hP
    exact_mod_cast h
  have hstrict : (n : ℝ) ^ (2 : ℕ) < (n : ℝ) ^ (2 : ℕ) := calc
    (n : ℝ) ^ (2 : ℕ) ≤ C * (n : ℝ) ^ (τ + ε) := hlower.trans hcost
    _ < (n : ℝ) ^ ε * (n : ℝ) ^ (τ + ε) :=
      mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hnpos _)
    _ = (n : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_add hnpos]
      have he : ε + (τ + ε) = 2 := by dsimp [ε] <;> ring
      rw [he]
      norm_num
  exact (lt_irrefl _ hstrict)

theorem rectangularAdmissibleExponent_bddBelow (F : Type*) [Field F] (k : ℝ) :
    BddBelow {τ : ℝ | RectangularAdmissibleExponent F k τ} :=
  ⟨2, fun _ h => rectangularAdmissibleExponent_two_le h⟩

theorem rectangularOmega_le_of_admissibleExponent {F : Type*} [Field F] {k τ : ℝ}
    (hτ : RectangularAdmissibleExponent F k τ) : rectangularOmega F k ≤ τ :=
  csInf_le (rectangularAdmissibleExponent_bddBelow F k) hτ

end

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ComplexArithmeticGrowth
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.Foundation.Arithmetic

theorem exists_power_cover {b n : ℕ} (hb : 2 ≤ b) (hn : 1 ≤ n) :
    ∃ k : ℕ, n ≤ b ^ k ∧ b ^ k ≤ b * n := by
  refine ⟨Nat.log b n + 1, (Nat.lt_pow_succ_log_self (by omega) n).le, ?_⟩
  rw [pow_succ']
  exact Nat.mul_le_mul_left b (Nat.pow_log_le_self b (by omega))

theorem geometric_cost_recurrence_bound (x : ℕ → ℝ) (a b d q : ℝ)
    (hx : 0 ≤ x 0) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (haq : a < q) (hdq : d ≤ q)
    (hstep : ∀ k, x (k + 1) ≤ a * x k + b * d ^ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ k, x k ≤ C * q ^ k := by
  let C := x 0 + b / (q - a) + 1
  have hgap : 0 < q - a := sub_pos.mpr haq
  have hfrac : 0 ≤ b / (q - a) := div_nonneg hb hgap.le
  have hC : 0 < C := by dsimp [C] <;> linarith
  have hcancel : (q - a) * (b / (q - a)) = b := by
    field_simp [ne_of_gt hgap]
  have hCfrac : b / (q - a) ≤ C := by dsimp [C] <;> linarith
  have hcoeff : a * C + b ≤ C * q := by
    have hmul := mul_le_mul_of_nonneg_left hCfrac hgap.le
    rw [hcancel] at hmul
    calc
      a * C + b ≤ a * C + (q - a) * C := add_le_add (le_refl _) hmul
      _ = C * q := by ring
  refine ⟨C, hC, ?_⟩
  intro k
  induction k with
  | zero => simp only [pow_zero, mul_one]; dsimp [C] <;> linarith
  | succ k ih =>
    calc
      x (k + 1) ≤ a * x k + b * d ^ k := hstep k
      _ ≤ a * (C * q ^ k) + b * q ^ k :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd hdq k) hb)
      _ = (a * C + b) * q ^ k := by ring
      _ ≤ (C * q) * q ^ k :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (hd.trans hdq) k)
      _ = C * q ^ (k + 1) := by rw [pow_succ]; ring

end MatrixMultiplication.Foundation.Arithmetic

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ComplexPolynomialPowerGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open Filter
open scoped Topology

namespace MatrixMultiplication.Foundation

theorem tendsto_affine_mul_geometric_zero (D C : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hq_one : q < 1) :
    Tendsto (fun n : ℕ => (D * (n : ℝ) + C) * q ^ n) atTop (𝓝 0) := by
  have hlinear := (tendsto_self_mul_const_pow_of_lt_one hq hq_one).const_mul D
  have hconstant := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq_one).const_mul C
  simpa only [mul_zero, add_zero, add_mul, mul_assoc] using hlinear.add hconstant

theorem power_le_of_eventually_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ᶠ n : ℕ in atTop, a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  by_contra hnot
  have hra : r < a := lt_of_not_ge hnot
  have ha : 0 < a := hr.trans_lt hra
  have hratio : 0 ≤ r / a := div_nonneg hr ha.le
  have hratio_one : r / a < 1 := (div_lt_one ha).2 hra
  have hsmall :=
    (tendsto_affine_mul_geometric_zero D C hratio hratio_one).eventually_lt_const
      (show (0 : ℝ) < 1 from zero_lt_one)
  rcases (h.and hsmall).exists with ⟨n, hbound, hlt⟩
  have hge : (1 : ℝ) ≤ (D * (n : ℝ) + C) * (r / a) ^ n := by
    rw [div_pow, ← mul_div_assoc]
    exact (le_div_iff₀ (pow_pos ha n)).2 (by simpa only [one_mul] using hbound)
  exact (not_lt_of_ge hge) hlt

theorem power_le_of_forall_pow_le_affine_mul_pow {a r D C : ℝ}
    (hr : 0 ≤ r)
    (h : ∀ n : ℕ, 0 < n → a ^ n ≤ (D * (n : ℝ) + C) * r ^ n) :
    a ≤ r := by
  apply power_le_of_eventually_pow_le_affine_mul_pow hr
  exact eventually_atTop.2 ⟨1, fun n hn => h n (Nat.zero_lt_one.trans_le hn)⟩

theorem power_le_of_forall_pow_le_mul_pow {a r C : ℝ}
    (hr : 0 ≤ r) (h : ∀ n : ℕ, 0 < n → a ^ n ≤ C * r ^ n) :
    a ≤ r := by
  apply power_le_of_forall_pow_le_affine_mul_pow (D := 0) (C := C) hr
  simpa only [zero_mul, zero_add] using h

end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_RectangularGrowth
attribute [-simp] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIncomingMasks.append_singletons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

theorem rectangular_power_cost_padding_bound
    {a b : ℕ} (ha : 2 ≤ a) {k s C : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hs : 0 ≤ s) (hC : 0 < C)
    (hpower : ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
      P.Correct ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ s) ^ t) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ P : MatrixAlgorithm F n (innerSize n k) n,
        P.Correct ∧ (P.cost : ℝ) ≤ D * (n : ℝ) ^ s := by
  have hapos : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  refine ⟨C * (a : ℝ) ^ s, mul_pos hC (Real.rpow_pos_of_pos hapos s), ?_⟩
  intro n hn
  obtain ⟨t, hnt, htn⟩ := MatrixMultiplication.Foundation.Arithmetic.exists_power_cover ha hn
  obtain ⟨P, hP, hcost⟩ := hpower t
  obtain ⟨Q, hQ, hQP⟩ := MatrixAlgorithm.exists_restrict
    hnt (innerSize_le_pow hk hnt hab) hnt P hP
  refine ⟨Q, hQ, ?_⟩
  calc
    (Q.cost : ℝ) ≤ (P.cost : ℝ) := by exact_mod_cast hQP
    _ ≤ C * ((a : ℝ) ^ s) ^ t := hcost
    _ = C * ((a ^ t : ℕ) : ℝ) ^ s := by
      rw [Real.rpow_pow_comm hapos.le, Nat.cast_pow]
    _ ≤ C * ((a : ℝ) * (n : ℝ)) ^ s :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast htn) hs) hC.le
    _ = (C * (a : ℝ) ^ s) * (n : ℝ) ^ s := by
      rw [Real.mul_rpow hapos.le (Nat.cast_nonneg n)]
      ring

theorem rectangularAdmissibleExponent_of_power_costs
    {a b : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hτ : 0 ≤ τ)
    (hpower : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
        P.Correct ∧ (P.cost : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t) :
    RectangularAdmissibleExponent F k τ := by
  intro ε hε
  obtain ⟨C, hC, hcost⟩ := hpower ε hε
  exact rectangular_power_cost_padding_bound ha hk hab (by linarith) hC hcost

theorem rectangularBlockCost_bound {a b R K : ℕ} (ha : 2 ≤ a)
    {τ ε : ℝ} (hε : 0 < ε)
    (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t,
      (rectangularBlockCost a b R K t : ℝ) ≤ C * ((a : ℝ) ^ (τ + ε)) ^ t := by
  have haone : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hrate : (R : ℝ) < (a : ℝ) ^ (τ + ε) :=
    hR.trans_lt (Real.rpow_lt_rpow_of_exponent_lt haone (by linarith))
  have hlarge : (a : ℝ) ^ τ ≤ (a : ℝ) ^ (τ + ε) :=
    Real.rpow_le_rpow_of_exponent_le haone.le (by linarith)
  have hin0 : (0 : ℝ) ≤ (a * b : ℕ) := Nat.cast_nonneg _
  have hd : 0 ≤ max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) :=
    hin0.trans (le_max_left _ _)
  apply MatrixMultiplication.Foundation.Arithmetic.geometric_cost_recurrence_bound
    (fun t => (rectangularBlockCost a b R K t : ℝ))
    (R : ℝ) (2 * K) (max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)))
    ((a : ℝ) ^ (τ + ε)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) hd hrate (max_le (hin.trans hlarge) (hout.trans hlarge))
  intro t
  simp only [rectangularBlockCost_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  have h1 : ((a : ℝ) * (b : ℝ)) ^ t ≤
      max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) ^ t := by
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Nat.cast_mul] using le_max_left ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ))
  have h2 : ((a : ℝ) ^ (2 : ℕ)) ^ t ≤
      max ((a * b : ℕ) : ℝ) ((a : ℝ) ^ (2 : ℕ)) ^ t :=
    pow_le_pow_left₀ (sq_nonneg _) (le_max_right _ _) t
  simp only [Nat.cast_mul] at h1 h2
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) (Nat.cast_nonneg K)]

theorem rectangular_power_programs_of_block_step {a b R K : ℕ}
    (hscalar : ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1)
    (hstep : ∀ m p : ℕ, ∀ P : MatrixAlgorithm F m p m, P.Correct →
      ∃ Q : MatrixAlgorithm F (a * m) (b * p) (a * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * (m * p + m ^ 2)) :
    ∀ t : ℕ, ∃ P : MatrixAlgorithm F (a ^ t) (b ^ t) (a ^ t),
      P.Correct ∧ P.cost ≤ rectangularBlockCost a b R K t := by
  intro t
  induction t with
  | zero => simpa using hscalar
  | succ t ih =>
    obtain ⟨P, hP, hcost⟩ := ih
    obtain ⟨Q, hQ, hQcost⟩ := hstep (a ^ t) (b ^ t) P hP
    have hbound : Q.cost ≤ rectangularBlockCost a b R K (t + 1) := by
      apply hQcost.trans
      simp only [rectangularBlockCost_succ, mul_pow, ← pow_mul, Nat.mul_comm t 2]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left R hcost) _
    have hresult : ∃ Q : MatrixAlgorithm F (a * a ^ t) (b * b ^ t) (a * a ^ t),
        Q.Correct ∧ Q.cost ≤ rectangularBlockCost a b R K (t + 1) := ⟨Q, hQ, hbound⟩
    exact (pow_succ' a t).symm ▸ ((pow_succ' b t).symm ▸ hresult)

theorem rectangularAdmissibleExponent_of_block_step
    {a b R K : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ)) (hτ : 0 ≤ τ)
    (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ)
    (hscalar : ∃ P : MatrixAlgorithm F 1 1 1, P.Correct ∧ P.cost ≤ 1)
    (hstep : ∀ m p : ℕ, ∀ P : MatrixAlgorithm F m p m, P.Correct →
      ∃ Q : MatrixAlgorithm F (a * m) (b * p) (a * m), Q.Correct ∧
        Q.cost ≤ R * P.cost + K * (m * p + m ^ 2)) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_power_costs ha hk hab hτ
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := rectangularBlockCost_bound (K := K) ha hε hR hin hout
  refine ⟨C, hC, ?_⟩
  intro t
  obtain ⟨P, hP, hcost⟩ := rectangular_power_programs_of_block_step hscalar hstep t
  exact ⟨P, hP, (by exact_mod_cast hcost : (P.cost : ℝ) ≤
    (rectangularBlockCost a b R K t : ℝ)).trans (hbound t)⟩

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_InitialState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation

namespace Arithmetic

variable {F : Type*} [Field F]

theorem rectangularAdmissibleExponent_of_rankAtMost
    {a b R : ℕ} (ha : 2 ≤ a) {k τ : ℝ} (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hτ : 0 ≤ τ) (hR : (R : ℝ) ≤ (a : ℝ) ^ τ)
    (hin : (a * b : ℕ) ≤ (a : ℝ) ^ τ)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ (a : ℝ) ^ τ) :
    RectangularAdmissibleExponent F k τ := by
  apply rectangularAdmissibleExponent_of_block_step
    (K := 2 * R * (2 * (a * b) + a ^ 2)) ha hk hab hτ hR hin hout
  · exact ⟨scalarAlgorithm F, scalarAlgorithm_correct F, (scalarAlgorithm_cost F).le⟩
  · intro m p P hP
    obtain ⟨Q, hQ, hcost⟩ := RecursiveBlock.rank_block_step hRank P hP
    refine ⟨Q, hQ, ?_⟩
    rw [hcost]
    nlinarith [Nat.zero_le (2 * R * (2 * (a * b) * m ^ 2 + a ^ 2 * (m * p)))]

theorem rectangular_rpow_omega_le_of_rankAtMost
    {a b R : ℕ} {B k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hRank : MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F) (Fin a) (Fin b) (Fin a)) R)
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ B) (hin : (a * b : ℕ) ≤ B)
    (hR : (R : ℝ) ≤ B) :
    (a : ℝ) ^ rectangularOmega F k ≤ B := by
  have ha1 : 1 < (a : ℝ) := by exact_mod_cast (by omega : 1 < a)
  have ha0 : 0 < (a : ℝ) := lt_trans zero_lt_one ha1
  have hB : 0 < B := (sq_pos_of_pos ha0).trans_le hout
  have hpow : (a : ℝ) ^ Real.logb a B = B :=
    Real.rpow_logb ha0 (ne_of_gt ha1) hB
  have hτ : 2 ≤ Real.logb (a : ℝ) B := by
    apply (Real.le_logb_iff_rpow_le ha1 hB).mpr
    simpa only [Real.rpow_two] using hout
  have hadm := rectangularAdmissibleExponent_of_rankAtMost ha hk hab hRank
    (by linarith : 0 ≤ Real.logb (a : ℝ) B)
    (hR.trans_eq hpow.symm) (hin.trans_eq hpow.symm) (hout.trans_eq hpow.symm)
  exact (Real.rpow_le_rpow_of_exponent_le ha1.le
    (rectangularOmega_le_of_admissibleExponent hadm)).trans_eq hpow

theorem rectangular_rpow_omega_le_of_rank_growth_oai
    {a b : ℕ} {q C k : ℝ} (ha : 2 ≤ a) (hk : 0 ≤ k)
    (hab : (a : ℝ) ^ k ≤ (b : ℝ))
    (hout : (a : ℝ) ^ (2 : ℕ) ≤ q) (hin : (a * b : ℕ) ≤ q)
    (R : ℕ → ℕ)
    (hRank : ∀ t, MatrixMultiplication.Foundation.Tensor.RankAtMost
      (MatrixMultiplication.Foundation.Tensor.matrixCoefficients (K := F)
        (Fin (a ^ t)) (Fin (b ^ t)) (Fin (a ^ t))) (R t))
    (hcost : ∀ t, (R t : ℝ) ≤ C * q ^ t) :
    (a : ℝ) ^ rectangularOmega F k ≤ q := by
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hq0 : 0 ≤ q := (sq_nonneg (a : ℝ)).trans hout
  apply power_le_of_forall_pow_le_mul_pow hq0 (C := max 1 C)
  intro t ht
  have hat : 2 ≤ a ^ t := ha.trans (le_self_pow (by omega) (Nat.ne_of_gt ht))
  have habt : ((a ^ t : ℕ) : ℝ) ^ k ≤ ((b ^ t : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_pow, ← Real.rpow_pow_comm ha0]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg a) k) hab t
  have hbase : ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t : ℕ) : ℝ) ^ (2 : ℕ) = ((a : ℝ) ^ (2 : ℕ)) ^ t := by
        rw [Nat.cast_pow, ← pow_mul, ← pow_mul, Nat.mul_comm t 2]
      _ ≤ q ^ t := by gcongr
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hinput : ((a ^ t * b ^ t : ℕ) : ℝ) ≤ max 1 C * q ^ t := by
    calc
      ((a ^ t * b ^ t : ℕ) : ℝ) = (((a * b : ℕ) : ℝ)) ^ t := by
        simp only [Nat.cast_mul, Nat.cast_pow, mul_pow]
      _ ≤ q ^ t := pow_le_pow_left₀ (Nat.cast_nonneg _) hin t
      _ ≤ max 1 C * q ^ t := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) C) (pow_nonneg hq0 t)
  have hcost' : (R t : ℝ) ≤ max 1 C * q ^ t :=
    (hcost t).trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) C)
      (pow_nonneg hq0 t))
  have h := rectangular_rpow_omega_le_of_rankAtMost hat hk habt
    (hRank t) hbase hinput hcost'
  simpa only [Nat.cast_pow, ← Real.rpow_pow_comm ha0] using h

end Arithmetic
end MatrixMultiplication

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldFiniteFamily

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

end MatrixMultiplication.AllFieldFiniteFamily

end
end

end MatrixAllFields

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth_oai.{u_1} := @OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.rectangular_rpow_omega_le_of_rank_growth_oai.{u_1}
