-- Prove2me | solution 1 for OAI.NCHitting.universal_hitting
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:36:45.728956+00:00
-- url     : https://prove2.me/submissions/d86aa93c-4141-4476-8568-565582b8d6c8

-- Generated from openai/math@1581d4c lean/OAI/Algebra/FormulaHitting/Hitting.lean:L86-L94
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.NCHitting.universal_hitting.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_NCHitting_universal_hitting) verbatim and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence
import Definitions.Def_OAI_Algebra_FormulaHitting_WordIndependence
import Definitions.Def_OAI_Algebra_FormulaHitting_RationalTransfer
import Definitions.Def_OAI_Algebra_FormulaHitting_Generator
import Definitions.Def_OAI_Algebra_FormulaHitting_JetMatrix
import Theorems.Thm_OAI_NCHitting_Formula_representation_card_le
import Theorems.Thm_OAI_NCHitting_Formula_representation_card_pos
import Theorems.Thm_OAI_NCHitting_Formula_size_le_one_iff
import Theorems.Thm_OAI_NCHitting_coeff_J
import Theorems.Thm_OAI_NCHitting_kernel_mul_linear
import Theorems.Thm_OAI_NCHitting_multiplicity_dimension_bound
import Theorems.Thm_OAI_NCHitting_polynomialEncode_eq_zero
import Theorems.Thm_OAI_NCHitting_sum_eq_sum_wordsOfLength
import Theorems.Thm_OAI_NCHitting_sum_wordsOfLength_succ
import Theorems.Thm_OAI_NCHitting_system_multiplicity

-- ---- from OAI.Algebra.FormulaHitting.Representation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace NCHitting

open Matrix

theorem automatonValue_add {F I : Type*} {n : ℕ} [Semiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (u u' v : I → F) (w : Word n) :
    automatonValue B (u + u') v w =
      automatonValue B u v w + automatonValue B u' v w := by
  induction w generalizing u u' with
  | nil => simp [automatonValue, add_dotProduct]
  | cons i w ih => simp [automatonValue, add_vecMul, ih]

theorem automatonValue_smul {F I : Type*} {n : ℕ} [CommSemiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (a : F) (u v : I → F) (w : Word n) :
    automatonValue B (a • u) v w = a * automatonValue B u v w := by
  induction w generalizing u with
  | nil => simp [automatonValue, smul_dotProduct]
  | cons i w ih => simp [automatonValue, smul_vecMul, ih]

theorem automatonValue_zero {F I : Type*} {n : ℕ} [Semiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (v : I → F) (w : Word n) :
    automatonValue B 0 v w = 0 := by
  induction w with
  | nil => simp [automatonValue]
  | cons i w ih => simp [automatonValue, ih]

theorem automatonValue_eq_matrix {F I : Type*} {n : ℕ}
    [Semiring F] [Fintype I] [DecidableEq I]
    (B : Fin n → Matrix I I F) (u v : I → F) (w : Word n) :
    automatonValue B u v w = u ⬝ᵥ (wordMatrix B w *ᵥ v) := by
  induction w generalizing u with
  | nil => simp [automatonValue, wordMatrix]
  | cons i w ih =>
    simp only [automatonValue, ih, wordMatrix, List.map_cons, List.prod_cons]
    rw [← dotProduct_mulVec, mulVec_mulVec]

theorem automatonValue_sumBlocks {F I J : Type*} {n : ℕ}
    [Semiring F] [Fintype I] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (u v : I → F) (u' v' : J → F) (w : Word n) :
    automatonValue (fun i => fromBlocks (A i) 0 0 (B i))
        (Sum.elim u u') (Sum.elim v v') w =
      automatonValue A u v w + automatonValue B u' v' w := by
  induction w generalizing u u' with
  | nil => simp [automatonValue, sumElim_dotProduct_sumElim]
  | cons i w ih =>
    simpa [automatonValue, vecMul_fromBlocks, Function.comp_def] using
      ih (u ᵥ* A i) (u' ᵥ* B i)

theorem automatonValue_productBlocks_general {F I J : Type*} {n : ℕ}
    [CommSemiring F] [Fintype I] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (u v : I → F) (u' b v' : J → F) (w : Word n) :
    automatonValue (productTransition A B v u') (Sum.elim u b)
        (Sum.elim ((u' ⬝ᵥ v') • v) v') w =
      convolution (automatonValue A u v) (automatonValue B u' v') w +
        automatonValue B b v' w := by
  induction w generalizing u b with
  | nil =>
    simp [automatonValue, convolution, sumElim_dotProduct_sumElim,
      dotProduct_smul, mul_comm]
  | cons i w ih =>
    rw [automatonValue]
    simp only [productTransition, vecMul_fromBlocks, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, vecMul_zero, add_zero, vecMul_vecMulVec]
    rw [ih, automatonValue_add, automatonValue_smul]
    simp only [convolution, automatonValue]
    ac_rfl

theorem automatonValue_productBlocks {F I J : Type*} {n : ℕ}
    [CommSemiring F] [Fintype I] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (u v : I → F) (u' v' : J → F) (w : Word n) :
    automatonValue (productTransition A B v u') (Sum.elim u 0)
        (Sum.elim ((u' ⬝ᵥ v') • v) v') w =
      convolution (automatonValue A u v) (automatonValue B u' v') w := by
  rw [automatonValue_productBlocks_general, automatonValue_zero, add_zero]

attribute [instance] AcyclicRepresentation.fintype AcyclicRepresentation.decidableEq

namespace AcyclicRepresentation

variable {F : Type*} {n : ℕ} [CommSemiring F]

theorem wordMatrix_entry_zero (R : AcyclicRepresentation F n)
    (w : Word n) (a b : R.State) (h : R.rank b < R.rank a + w.length) :
    wordMatrix R.B w a b = 0 := by
  induction w generalizing a with
  | nil =>
    have hne : a ≠ b := by intro he; subst b; simp at h
    simp [wordMatrix, hne]
  | cons i w ih =>
    simp only [wordMatrix, List.map_cons, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : R.rank c ≤ R.rank a
    · rw [R.upper i a c hc, zero_mul]
    · have hbc : R.rank b < R.rank c + w.length := by
        simp only [List.length_cons] at h
        omega
      rw [show (List.map R.B w).prod c b = 0 from ih c hbc, mul_zero]

theorem wordMatrix_eq_zero (R : AcyclicRepresentation F n)
    (w : Word n) (h : Fintype.card R.State ≤ w.length) : wordMatrix R.B w = 0 := by
  ext a b
  apply R.wordMatrix_entry_zero w a b
  have hb := R.rank_lt b
  omega

theorem value_eq_matrix (R : AcyclicRepresentation F n) (w : Word n) :
    R.value w = R.u ⬝ᵥ (wordMatrix R.B w *ᵥ R.v) :=
  automatonValue_eq_matrix R.B R.u R.v w

theorem add_value (R S : AcyclicRepresentation F n) (w : Word n) :
    (R.add S).value w = R.value w + S.value w :=
  automatonValue_sumBlocks R.B S.B R.u R.v S.u S.v w

theorem mul_value (R S : AcyclicRepresentation F n) (w : Word n) :
    (R.mul S).value w = convolution R.value S.value w :=
  automatonValue_productBlocks R.B S.B R.u R.v S.u S.v w

theorem scalar_value (a : F) (w : Word n) :
    (scalar (n := n) a).value w = if w = [] then a else 0 := by
  cases w with
  | nil =>
    change (∑ _ : Unit, a * 1) = a
    simp
  | cons i w =>
    change automatonValue (fun _ : Fin n => (0 : Matrix Unit Unit F))
      ((fun _ : Unit => a) ᵥ* 0) (fun _ => 1) w = 0
    rw [vecMul_zero, automatonValue_zero]

theorem variable_value (i : Fin n) (w : Word n) :
    (ofVariable (F := F) i).value w = if w = [i] then 1 else 0 := by
  change automatonValue
    (fun j (a b : Fin 2) => if a = 0 ∧ b = 1 ∧ j = i then (1 : F) else 0)
    (fun a : Fin 2 => if a = 0 then 1 else 0)
    (fun a : Fin 2 => if a = 1 then 1 else 0) w = _
  cases w with
  | nil => simp [automatonValue, dotProduct]
  | cons j w =>
    cases w with
    | nil =>
      simp [automatonValue, vecMul, dotProduct, Fin.sum_univ_two]
    | cons k w =>
      have hz : ((ofVariable (F := F) i).u ᵥ* (ofVariable i).B j) ᵥ*
          (ofVariable i).B k = 0 := by
        change ((fun a : Fin 2 => if a = 0 then (1 : F) else 0) ᵥ*
          (fun a b : Fin 2 => if a = 0 ∧ b = 1 ∧ j = i then 1 else 0)) ᵥ*
          (fun a b : Fin 2 => if a = 0 ∧ b = 1 ∧ k = i then 1 else 0) = 0
        ext a
        change _ = (0 : F)
        fin_cases a <;>
          simp [vecMul, dotProduct, Fin.sum_univ_two]
      rw [ite_eq_right (show (j :: k :: w : Word n) ≠ [i] by simp)]
      change automatonValue (ofVariable (F := F) i).B
        (((ofVariable i).u ᵥ* (ofVariable i).B j) ᵥ* (ofVariable i).B k)
        (ofVariable i).v w = 0
      rw [hz, automatonValue_zero]

end AcyclicRepresentation

theorem Formula.representation_correct {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) (w : Word n) : f.representation.value w = f.coeff w := by
  induction f generalizing w with
  | scalar a => exact AcyclicRepresentation.scalar_value a w
  | var i => exact AcyclicRepresentation.variable_value i w
  | add f g ihf ihg =>
    simp only [Formula.representation, AcyclicRepresentation.add_value,
      Formula.coeff, ihf, ihg]
  | mul f g ihf ihg =>
    simp only [Formula.representation, AcyclicRepresentation.mul_value, Formula.coeff]
    congr 1 <;> funext w <;> first | exact ihf w | exact ihg w

theorem Formula.coeff_zero_of_representation_dimension_le
    {F : Type*} {n : ℕ} [CommSemiring F] (f : Formula F n) (w : Word n)
    (h : Fintype.card f.representation.State ≤ w.length) : f.coeff w = 0 := by
  rw [← f.representation_correct w, f.representation.value_eq_matrix,
    f.representation.wordMatrix_eq_zero w h]
  simp

end NCHitting

end OAI

-- ---- from OAI.Algebra.FormulaHitting.System ----
namespace OAI

noncomputable section
namespace NCHitting
namespace AcyclicRepresentation

open Matrix
variable {F : Type*} {n : ℕ} [Field F] [CharZero F]

omit [CharZero F] in
theorem J_sum {I : Type*} (i : ℕ) (s : Finset I) (f : I → PowerSeries F) :
    J i (∑ a ∈ s, f a) = ∑ a ∈ s, J i (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, J_add, ih]

omit [CharZero F] in
theorem J_C_mul (i : ℕ) (c : F) (f : PowerSeries F) :
    J i (PowerSeries.C c * f) = PowerSeries.C c * J i f := by
  simpa only [PowerSeries.smul_eq_C_mul] using J_smul i c f

omit [CharZero F] in
theorem denominator_eq (i : Fin n) : denominator (F := F) n =
    (Polynomial.X + Polynomial.C ((i.val + 1 : ℕ) : F)) * cofactor i := by
  exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm

omit [CharZero F] in
theorem denominator_degree : (denominator (F := F) n).natDegree ≤ n := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  simp only [Polynomial.natDegree_X_add_C]
  simp

omit [CharZero F] in
theorem cofactor_degree (i : Fin n) : (cofactor (F := F) i).natDegree ≤ n - 1 := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  simp only [Polynomial.natDegree_X_add_C]
  simp

omit [CharZero F] in
theorem systemNumerator_degree (R : AcyclicRepresentation F n) (a b : R.State) :
    (R.systemNumerator a b).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_le _ _).trans (cofactor_degree i)

theorem denominator_eval_zero_ne : (denominator (F := F) n).eval 0 ≠ 0 := by
  simp only [denominator, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, zero_add]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i.val)

theorem denominator_mul_kernel (i : Fin n) :
    (denominator (F := F) n : PowerSeries F) * kernel (i.val + 1) =
      (cofactor (F := F) i : PowerSeries F) := by
  rw [denominator_eq i]
  simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
  calc
    (PowerSeries.X + PowerSeries.C ((i.val + 1 : ℕ) : F)) *
        (cofactor (F := F) i : PowerSeries F) * kernel (i.val + 1) =
        (cofactor (F := F) i : PowerSeries F) *
          (kernel (i.val + 1) * (PowerSeries.X + PowerSeries.C ((i.val + 1 : ℕ) : F))) := by ring
    _ = _ := by rw [kernel_mul_linear _ (Nat.succ_ne_zero _)]; simp

omit [CharZero F] in
theorem polynomial_coe_sum {I : Type*} [Fintype I] (p : I → Polynomial F) :
    ((∑ i, p i : Polynomial F) : PowerSeries F) = ∑ i, (p i : PowerSeries F) :=
  map_sum Polynomial.coeToPowerSeries.ringHom p Finset.univ

theorem denominator_mul_systemMatrix (R : AcyclicRepresentation F n) (a b : R.State) :
    (denominator (F := F) n : PowerSeries F) * R.systemMatrix a b =
      (R.systemNumerator a b : PowerSeries F) := by
  simp only [systemMatrix, systemNumerator, polynomial_coe_sum, Polynomial.coe_mul,
    Polynomial.coe_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, denominator_mul_kernel]

omit [CharZero F] in
theorem systemLevel_wordSum (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) :
    R.systemLevel k a b = ∑ w ∈ wordsOfLength n k,
      PowerSeries.C (wordMatrix R.B w a b) * wordSeries w := by
  induction k generalizing a b with
  | zero =>
    by_cases h : a = b <;>
      simp [systemLevel, wordsOfLength, wordMatrix, Matrix.one_apply, h]
  | succ k ih =>
    rw [sum_wordsOfLength_succ]
    simp only [systemLevel, ih, J_sum, J_C_mul, wordSeries_cons,
      wordMatrix, List.map_cons, List.prod_cons, Matrix.mul_apply,
      map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm

omit [CharZero F] in
theorem contract_wordMatrix (R : AcyclicRepresentation F n) (w : Word n) :
    R.contract ((wordMatrix R.B w).map PowerSeries.C) = PowerSeries.C (R.value w) := by
  rw [R.value_eq_matrix]
  simp [contract, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

omit [CharZero F] in
theorem systemLevel_eq_sum (R : AcyclicRepresentation F n) (k : ℕ) :
    R.systemLevel k = ∑ w ∈ wordsOfLength n k,
      wordSeries (F := F) w • (wordMatrix R.B w).map PowerSeries.C := by
  apply Matrix.ext
  intro a b
  simpa [Matrix.sum_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using
    R.systemLevel_wordSum k a b

omit [CharZero F] in
theorem fundamentalMatrix_eq_sum (R : AcyclicRepresentation F n) :
    R.fundamentalMatrix =
      ∑ k ∈ Finset.range (Fintype.card R.State), R.systemLevel k := by
  apply Matrix.ext
  intro a b
  simp [fundamentalMatrix, Matrix.sum_apply]

omit [CharZero F] in
theorem contract_fundamentalMatrix (R : AcyclicRepresentation F n) :
    R.contract R.fundamentalMatrix =
      ∑ k ∈ Finset.range (Fintype.card R.State), ∑ w ∈ wordsOfLength n k,
        PowerSeries.C (R.value w) * wordSeries w := by
  rw [fundamentalMatrix_eq_sum]
  simp [systemLevel_eq_sum, contract_wordMatrix, smul_eq_mul, mul_comm]

omit [CharZero F] in
theorem systemLevel_entry_zero (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) (h : R.rank b < R.rank a + k) :
    R.systemLevel k a b = 0 := by
  induction k generalizing a with
  | zero =>
    have hne : a ≠ b := by intro he; subst b; simp at h
    simp [systemLevel, hne]
  | succ k ih =>
    simp only [systemLevel]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : R.rank c ≤ R.rank a
    · simp [R.upper i a c hc]
    · have hbc : R.rank b < R.rank c + k := by omega
      rw [ih c hbc]
      simp

omit [CharZero F] in
theorem systemLevel_eq_zero (R : AcyclicRepresentation F n)
    (k : ℕ) (h : Fintype.card R.State ≤ k) : R.systemLevel k = 0 := by
  apply Matrix.ext
  intro a b
  apply R.systemLevel_entry_zero k a b
  have hb := R.rank_lt b
  omega

theorem derivative_systemLevel (R : AcyclicRepresentation F n)
    (k : ℕ) (a b : R.State) :
    PowerSeries.derivative (R := F) (R.systemLevel (k + 1) a b) =
      (R.systemMatrix * R.systemLevel k) a b := by
  simp only [systemLevel, map_sum, Derivation.leibniz, smul_eq_mul, derivative_J,
    PowerSeries.derivative_C, systemMatrix, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [CharZero F] in
theorem fundamentalMatrix_constant (R : AcyclicRepresentation F n)
    (hm : 0 < Fintype.card R.State) :
    R.fundamentalMatrix.map PowerSeries.constantCoeff = 1 := by
  apply Matrix.ext
  intro a b
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Matrix.map_apply, fundamentalMatrix, hk,
    Finset.sum_range_succ']
  simp [systemLevel, Matrix.one_apply]

omit [CharZero F] in
theorem fundamentalMatrix_isUnit (R : AcyclicRepresentation F n)
    (hm : 0 < Fintype.card R.State) : IsUnit R.fundamentalMatrix := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply (PowerSeries.isUnit_iff_constantCoeff).mpr
  have hc : PowerSeries.constantCoeff R.fundamentalMatrix.det = 1 := by
    rw [RingHom.map_det]
    change (R.fundamentalMatrix.map PowerSeries.constantCoeff).det = 1
    rw [R.fundamentalMatrix_constant hm, Matrix.det_one]
  rw [hc]
  exact isUnit_one

theorem fundamentalMatrix_derivative (R : AcyclicRepresentation F n) :
    R.fundamentalMatrix.map (PowerSeries.derivative (R := F)) =
      R.systemMatrix * R.fundamentalMatrix := by
  apply Matrix.ext
  intro a b
  let D : ℕ → PowerSeries F := fun k => PowerSeries.derivative (R := F) (R.systemLevel k a b)
  have hD0 : D 0 = 0 := by
    by_cases h : a = b <;> simp [D, systemLevel, h]
  have hDm : D (Fintype.card R.State) = 0 := by
    simp [D, R.systemLevel_eq_zero _ (le_refl _)]
  have hshift : (∑ k ∈ Finset.range (Fintype.card R.State), D k) =
      ∑ k ∈ Finset.range (Fintype.card R.State), D (k + 1) := by
    have hleft := Finset.sum_range_succ D (Fintype.card R.State)
    have hright := Finset.sum_range_succ' D (Fintype.card R.State)
    simpa [hD0, hDm] using hleft.symm.trans hright
  simp only [Matrix.map_apply, fundamentalMatrix, map_sum]
  change (∑ k ∈ Finset.range (Fintype.card R.State), D k) = _
  rw [hshift]
  simp only [D, derivative_systemLevel, Matrix.mul_apply, fundamentalMatrix,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem fundamentalMatrix_polynomial_system (R : AcyclicRepresentation F n)
    (a b : R.State) :
    (denominator (F := F) n : PowerSeries F) *
        PowerSeries.derivative (R := F) (R.fundamentalMatrix a b) =
      ∑ c : R.State, (R.systemNumerator a c : PowerSeries F) *
        R.fundamentalMatrix c b := by
  have hder := congrFun (congrFun R.fundamentalMatrix_derivative a) b
  change PowerSeries.derivative (R := F) (R.fundamentalMatrix a b) =
    ∑ c : R.State, R.systemMatrix a c * R.fundamentalMatrix c b at hder
  rw [hder, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [← mul_assoc, denominator_mul_systemMatrix]

end AcyclicRepresentation

theorem Formula.system_output {F : Type*} {n : ℕ} [Field F] [CharZero F]
    (f : Formula F n) :
    f.representation.contract f.representation.fundamentalMatrix =
      ∑ k ∈ Finset.range (Fintype.card f.representation.State),
        ∑ w ∈ wordsOfLength n k, PowerSeries.C (f.coeff w) * wordSeries w := by
  simp only [AcyclicRepresentation.contract_fundamentalMatrix, Formula.representation_correct]

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.Evaluation ----
namespace OAI

namespace NCHitting

attribute [local instance] OAI.NCHitting.instDecidableEqFreeMonoidFin_oAI
namespace Formula

theorem eval_eq_lift {F A : Type*} {n : ℕ} [CommSemiring F] [Semiring A]
    [Algebra F A] (f : Formula F n) (T : Fin n → A) :
    f.eval (algebraMap F A) T =
      MonoidAlgebra.lift F A (FreeMonoid (Fin n)) (FreeMonoid.lift T) f.monoidPolynomial := by
  induction f with
  | scalar a => simp [eval, monoidPolynomial, Algebra.smul_def]
  | var i => simp [eval, monoidPolynomial]
  | add f g ihf ihg => simp [eval, monoidPolynomial, ihf, ihg]
  | mul f g ihf ihg => simp [eval, monoidPolynomial, ihf, ihg]

theorem eval_eq_sum {F A : Type*} {n : ℕ} [CommSemiring F] [Semiring A]
    [Algebra F A] (f : Formula F n) (T : Fin n → A) :
    f.eval (algebraMap F A) T =
      f.polynomial.sum (fun w a => algebraMap F A a * (w.map T).prod) := by
  rw [eval_eq_lift, MonoidAlgebra.lift_apply']
  have hcoeff : f.monoidPolynomial.coeff = f.polynomial := by
    ext w
    exact monoidPolynomial_coeff f w
  rw [hcoeff]
  apply Finset.sum_congr rfl
  intro w hw
  change algebraMap F A (f.coeff w) * FreeMonoid.lift T w =
    algebraMap F A (f.coeff w) * (w.toList.map T).prod
  rw [FreeMonoid.lift_apply]

end Formula
end NCHitting

end OAI

-- ---- from OAI.Algebra.FormulaHitting.FormulaSeries ----
namespace OAI

noncomputable section
namespace NCHitting
namespace Formula

variable {F : Type*} {n : ℕ} [Field F]

theorem series_eq_smul_sum (f : Formula F n) :
    f.series = f.polynomial.sum (fun w a => a • wordSeries w) := by
  simp only [series, PowerSeries.smul_eq_C_mul]

theorem series_eq_sum_of_cutoff (f : Formula F n) (d : ℕ)
    (hcut : ∀ w, d ≤ w.length → f.coeff w = 0) :
    f.series = ∑ k ∈ Finset.range d, ∑ w ∈ wordsOfLength n k,
      PowerSeries.C (f.coeff w) * wordSeries w := by
  exact sum_eq_sum_wordsOfLength f.polynomial hcut _ (by intro w; simp)

end Formula
end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.SystemOutput ----
namespace OAI

namespace NCHitting

theorem Formula.system_output_eq_series {F : Type*} {n : ℕ}
    [Field F] [CharZero F] (f : Formula F n) :
    f.representation.contract f.representation.fundamentalMatrix = f.series := by
  rw [f.system_output, f.series_eq_sum_of_cutoff
    (Fintype.card f.representation.State) f.coeff_zero_of_representation_dimension_le]

end NCHitting

end OAI

-- ---- from OAI.Algebra.FormulaHitting.WordIndependence ----
namespace OAI

noncomputable section
open Polynomial PowerSeries
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
private theorem linearCombination_eq_polynomialEncode (c : PolyWords F n) :
    Finsupp.linearCombination F[X] (wordSeries (F := F) (n := n)) c = polynomialEncode c := by
  simp [Finsupp.linearCombination_apply, polynomialEncode, Finsupp.liftAddHom_apply,
    Algebra.smul_def, PowerSeries.algebraMap_apply']

theorem wordSeries_polynomial_independent :
    LinearIndependent F[X] (wordSeries (F := F) (n := n)) := by
  rw [linearIndependent_iff]
  intro c hc
  apply polynomialEncode_eq_zero (c.support.sup List.length) c
  · intro w hw
    exact Finset.le_sup (Finsupp.mem_support_iff.mpr hw)
  · rwa [linearCombination_eq_polynomialEncode] at hc

theorem wordSeries_independent : LinearIndependent F (wordSeries (F := F) (n := n)) :=
  wordSeries_polynomial_independent.restrict_scalars' F

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.SeriesFaithfulness ----
namespace OAI

namespace NCHitting
namespace Formula

variable {F : Type*} {n : ℕ} [Field F] [CharZero F]

theorem series_eq_zero_iff (f : Formula F n) : f.series = 0 ↔ f.coeff = 0 := by
  constructor
  · intro h
    have hc : Finsupp.linearCombination F (wordSeries (F := F) (n := n))
        f.polynomial = 0 := by
      simpa only [Finsupp.linearCombination_apply] using
        (f.series_eq_smul_sum.symm.trans h)
    have hp : f.polynomial = 0 :=
      (linearIndependent_iff.mp (wordSeries_independent (F := F) (n := n))) f.polynomial hc
    funext w
    exact congrArg (fun p : Word n →₀ F => p w) hp
  · intro h
    have hp : f.polynomial = 0 := by
      ext w
      exact congrFun h w
    simp [series, hp]

theorem series_ne_zero (f : Formula F n) (hf : f.coeff ≠ 0) : f.series ≠ 0 :=
  mt f.series_eq_zero_iff.mp hf

end Formula
end NCHitting

end OAI

-- ---- from OAI.Algebra.FormulaHitting.Generator ----
namespace OAI

namespace NCHitting

theorem dimension_eq {n s : ℕ} (hns : 2 ≤ n * s) :
    dimension n s = 2 * n * s ^ 2 := by
  unfold dimension
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    norm_num at hns
  · rfl

theorem generator_one (i : Fin 1) (r q : Fin (dimension 1 1)) :
    generator 1 1 i r q = 1 := by simp [generator]

theorem generator_entry {n s : ℕ} (hns : 2 ≤ n * s)
    (i : Fin n) (r q : Fin (dimension n s)) :
    generator n s i r q = matrixEntry (i.val + 1) r.val q.val := by
  have h : ¬(n = 1 ∧ s = 1) := by rintro ⟨rfl, rfl⟩; norm_num at hns
  simp [generator, h]

end NCHitting

end OAI

-- ---- from OAI.Algebra.FormulaHitting.JetMatrix ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

noncomputable section
namespace NCHitting

open Matrix

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem jet_eq_zero_iff (d : ℕ) (a : PowerSeries F) :
    jet d a = 0 ↔ ∀ r < d, PowerSeries.coeff r a = 0 := by
  constructor
  · intro h r hr
    exact congrFun h ⟨r, hr⟩
  · intro h
    ext r
    exact h r.val r.isLt

omit [CharZero F] in
theorem jet_ne_zero_of_order_lt (d : ℕ) (a : PowerSeries F)
    (horder : a.order < (d : ℕ∞)) : jet d a ≠ 0 := by
  intro h
  exact (not_le_of_gt horder)
    (PowerSeries.nat_le_order a d ((jet_eq_zero_iff d a).mp h))

theorem integrationMatrix_apply (d i : ℕ) (r q : Fin d) :
    integrationMatrix (F := F) d i r q =
      if q.val < r.val then
        (-1 : F) ^ (r.val - q.val - 1) /
          ((r.val : F) * (i : F) ^ (r.val - q.val))
      else 0 := by
  by_cases h : q.val < r.val <;> simp [integrationMatrix, matrixEntry, h]

theorem jet_J (d i : ℕ) (a : PowerSeries F) :
    jet d (J i a) = integrationMatrix d i *ᵥ jet d a := by
  ext r
  rw [jet_apply, coeff_J]
  simp only [Matrix.mulVec, dotProduct, integrationMatrix_apply, jet_apply]
  let term := fun q =>
    (if q < r.val then (-1 : F) ^ (r.val - q - 1) /
      ((r.val : F) * (i : F) ^ (r.val - q)) else 0) * PowerSeries.coeff q a
  change _ = ∑ q : Fin d, term q.val
  rw [Fin.sum_univ_eq_sum_range term d]
  calc
    _ = ∑ q ∈ Finset.range r.val, term q := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [term, ite_eq_left (Finset.mem_range.mp hq)]
    _ = ∑ q ∈ Finset.range d, term q := by
      apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt r.isLt))
      intro q hqd hqr
      have h : ¬q < r.val := by simpa using hqr
      simp [term, h]

theorem jet_wordSeries {n : ℕ} (d : ℕ) (w : Word n) :
    jet d (wordSeries (F := F) w) =
      (w.map (fun i => integrationMatrix (F := F) d (i.val + 1))).prod *ᵥ
        jet d (1 : PowerSeries F) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordSeries_cons, jet_J, ih]
    simp only [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

omit [CharZero F] in
theorem generator_cast_eq_integrationMatrix {n s : ℕ} (hns : 2 ≤ n * s)
    (i : Fin n) :
    (fun r q => (generator n s i r q : F)) =
      integrationMatrix (F := F) (dimension n s) (i.val + 1) := by
  ext r q
  simp only [integrationMatrix, generator_entry hns]

theorem Formula.jet_wordSum_eq_eval_mulVec {n : ℕ} (f : Formula F n) (d : ℕ) :
    jet d (f.polynomial.sum fun w a => a • wordSeries (F := F) w) =
      f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
        (fun i => integrationMatrix (F := F) d (i.val + 1)) *ᵥ
          jet d (1 : PowerSeries F) := by
  rw [Formula.eval_eq_sum]
  simp only [Finsupp.sum, map_sum, map_smul, Matrix.sum_mulVec,
    ← Algebra.smul_def, Matrix.smul_mulVec, jet_wordSeries]

theorem Formula.eval_ne_zero_of_jet_wordSum_ne_zero {n : ℕ}
    (f : Formula F n) (d : ℕ)
    (hjet : jet d (f.polynomial.sum fun w a => a • wordSeries (F := F) w) ≠ 0) :
    f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
      (fun i => integrationMatrix (F := F) d (i.val + 1)) ≠ 0 := by
  intro h
  apply hjet
  rw [f.jet_wordSum_eq_eval_mulVec d, h, Matrix.zero_mulVec]

theorem Formula.eval_ne_zero_of_jet_series_ne_zero {n : ℕ} (f : Formula F n) (d : ℕ)
    (hjet : jet d f.series ≠ 0) :
    f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
      (fun i => integrationMatrix (F := F) d (i.val + 1)) ≠ 0 := by
  apply f.eval_ne_zero_of_jet_wordSum_ne_zero d
  rwa [← f.series_eq_smul_sum]

theorem Formula.eval_generator_ne_zero_of_jet_series_ne_zero {n s : ℕ}
    (f : Formula F n) (hns : 2 ≤ n * s)
    (hjet : jet (dimension n s) f.series ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  have hT : (fun (i : Fin n) r q => (generator n s i r q : F)) =
      (fun i => integrationMatrix (F := F) (dimension n s) (i.val + 1)) := by
    funext i
    exact generator_cast_eq_integrationMatrix hns i
  rw [hT]
  exact f.eval_ne_zero_of_jet_series_ne_zero (dimension n s) hjet

end NCHitting

end

end OAI

-- ---- from OAI.Algebra.FormulaHitting.Hitting ----
namespace OAI

noncomputable section
namespace NCHitting

open Matrix PowerSeries

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem AcyclicRepresentation.scalarOutput_eq_contract {n : ℕ}
    (R : AcyclicRepresentation F n) :
    systemScalarOutput R.u R.v R.fundamentalMatrix =
      R.contract R.fundamentalMatrix := by
  simp only [systemScalarOutput, AcyclicRepresentation.contract,
    LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem Formula.series_order_lt {n : ℕ} (f : Formula F n) (hn : 0 < n)
    (hf : f.coeff ≠ 0) :
    f.series.order.toNat <
      (n-1) * (Fintype.card f.representation.State).choose 2 +
        Fintype.card f.representation.State := by
  let R := f.representation
  have hq : AcyclicRepresentation.denominator (F := F) n ≠ 0 := by
    intro hz
    have he := AcyclicRepresentation.denominator_eval_zero_ne (F := F) (n := n)
    exact he (by rw [hz, Polynomial.eval_zero])
  have ho : systemScalarOutput R.u R.v R.fundamentalMatrix = f.series :=
    R.scalarOutput_eq_contract.trans f.system_output_eq_series
  have hbound := system_multiplicity n hn
    (AcyclicRepresentation.denominator (F := F) n) R.systemNumerator R.u R.v
    R.fundamentalMatrix (AcyclicRepresentation.denominator_degree (F := F) (n := n))
    hq R.systemNumerator_degree
    (R.fundamentalMatrix_isUnit f.representation_card_pos)
    R.fundamentalMatrix_polynomial_system
    (by rw [ho]; exact f.series_ne_zero hf)
  rwa [ho] at hbound

theorem Formula.eval_generator_one_ne_zero (f : Formula F 1)
    (hs : f.size ≤ 1) (hf : f.coeff ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension 1 1)))
      (fun i r q => (generator 1 1 i r q : F)) ≠ 0 := by
  let r : Fin (dimension 1 1) := ⟨0, by decide⟩
  rcases (Formula.size_le_one_iff f).mp hs with ⟨a, rfl⟩ | ⟨i, rfl⟩
  · intro hz
    have ha : a = 0 := by
      have he := congrFun (congrFun hz r) r
      simpa [Formula.eval, Matrix.scalar_apply] using he
    apply hf
    funext w
    simp [Formula.coeff, ha]
  · intro hz
    have he := congrFun (congrFun hz r) r
    simp [Formula.eval, generator_one] at he

theorem Formula.eval_generator_ne_zero {n s : ℕ} (f : Formula F n)
    (hn : 0 < n) (hs : 0 < s) (hsize : f.size ≤ s) (hf : f.coeff ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  by_cases he : n = 1 ∧ s = 1
  · rcases he with ⟨rfl, rfl⟩
    exact f.eval_generator_one_ne_zero hsize hf
  · have hns : 2 ≤ n*s := by
      have hnle : n ≤ n*s := by simpa using Nat.mul_le_mul_left n hs
      have hsle : s ≤ n*s := by simpa using Nat.mul_le_mul_right s hn
      omega
    have hm : Fintype.card f.representation.State ≤ 2*s :=
      f.representation_card_le.trans (Nat.mul_le_mul_left 2 hsize)
    have hbound : f.series.order.toNat < dimension n s := by
      rw [dimension_eq hns]
      exact (f.series_order_lt hn hf).trans_le (multiplicity_dimension_bound hn hs hm)
    apply f.eval_generator_ne_zero_of_jet_series_ne_zero hns
    apply jet_ne_zero_of_order_lt
    rw [← PowerSeries.coe_toNat_order (f.series_ne_zero hf), ENat.natCast_lt_natCast]
    exact hbound

theorem universal_hitting (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (F : Type*) [Field F] [CharZero F] (f : Formula F n)
    (hsize : f.size ≤ s) (hf : ∃ w, f.coeff w ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  apply f.eval_generator_ne_zero hn hs hsize
  intro hz
  obtain ⟨w, hw⟩ := hf
  exact hw (congrFun hz w)

end NCHitting

end

end OAI

-- ---- mission target ----
open OAI OAI.NCHitting
universe u_2
open Matrix PowerSeries

namespace OAI
namespace NCHitting
theorem _root_.solution (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (F : Type u_2) [Field F] [CharZero F] (f : Formula F n)
    (hsize : f.size ≤ s) (hf : ∃ w, f.coeff w ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  first
    | exact OAI.NCHitting.universal_hitting n s hn hs F f hsize hf
    | exact OAI.NCHitting.universal_hitting
    | (apply OAI.NCHitting.universal_hitting <;> assumption)
    | (intros; apply OAI.NCHitting.universal_hitting <;> assumption)
end NCHitting
end OAI
