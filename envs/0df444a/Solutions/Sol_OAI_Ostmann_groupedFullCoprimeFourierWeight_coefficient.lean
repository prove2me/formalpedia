-- Prove2me | solution 1 for OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:39:02.35432+00:00
-- url     : https://prove2.me/submissions/572a186a-1431-4bbf-b4b1-60ff4b035a0a

import Mathlib
import Definitions.Def_OAIQ095D004
import Definitions.Def_OAIQ095D005

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ArithmeticSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Arithmetic support at a reversing node

These are the elementary support facts preceding the progression estimate
in Section 8. The numerator is automatically coprime to inherited slots;
the remaining condition at a new prime is exactly nondivisibility by its square.
-/

namespace Ostmann

theorem reversal_numerator_coprime (v w HL HR : ℤ)
    (hLR : IsCoprime HL HR) (hv : IsCoprime v HL) (hw : IsCoprime w HR) :
    IsCoprime (v * HR - w * HL) HL ∧ IsCoprime (v * HR - w * HL) HR := by
  constructor
  · exact IsCoprime.sub_mul_right_left_iff.mpr (hv.mul_left hLR.symm)
  · exact IsCoprime.mul_sub_right_left_iff.mpr (hw.mul_left hLR)

/-- Both the inserted integer and its compensation product inherit all required coprimalities. -/
theorem reversal_inherited_coprime (v w HL HR s u p : ℤ)
    (hLR : IsCoprime HL HR) (hv : IsCoprime v HL) (hw : IsCoprime w HR)
    (hrel : v * HR - w * HL = s * u * p) :
    IsCoprime p (HL * HR) ∧ IsCoprime u (HL * HR) := by
  obtain ⟨hL, hR⟩ := reversal_numerator_coprime v w HL HR hLR hv hw
  have hboth := hL.mul_right hR
  rw [hrel] at hboth
  exact ⟨hboth.of_mul_left_right, hboth.of_mul_left_left.of_mul_left_right⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ClearedHistoryPivot
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructed integer numerators for the recursive pivot substitutions -/

namespace Ostmann

open scoped BigOperators Classical

namespace ClearedHistoryValue

variable {σ : Type*}

theorem eval_variable (i : σ) (x : σ → ℚ) : (ofVariable i).eval x = x i := by
  simp only [eval, ofVariable, MvPolynomial.eval₂_X, Int.cast_one, div_one]

theorem eval_constant (a : ℤ) (x : σ → ℚ) : (constant a).eval x = a := by
  simp only [eval, constant, MvPolynomial.eval₂_C, Int.cast_one, div_one]
  rfl

theorem eval_prod {I : Type*} (S : Finset I) (f : I → ClearedHistoryValue σ) (x : σ → ℚ) :
    (prod S f).eval x = ∏ i ∈ S, (f i).eval x := by
  simp only [eval, prod, MvPolynomial.eval₂_eq_eval_map, map_prod, Finset.prod_div_distrib]
  push_cast
  rfl

theorem eval_pivot (left right : ClearedHistoryValue σ) (v w s : ℤ) (hs : s ≠ 0)
    (x : σ → ℚ) :
    (pivot left right v w s hs).eval x = (v * right.eval x - w * left.eval x) / s := by
  have hL : (left.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr left.denominator_ne_zero
  have hR : (right.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr right.denominator_ne_zero
  have hS : (s : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs
  simp only [eval, pivot, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, Int.coe_castRingHom, Int.cast_mul]
  field_simp

/-- Polynomial evaluation at an integer assignment is the numerator of the
actual rational value. The equality is useful on the integrality support. -/
theorem integer_value_cleared (F : ClearedHistoryValue σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.eval (fun i => (x i : ℚ)) = y) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator = F.denominator * y := by
  have hden : (F.denominator : ℚ) ≠ 0 := Int.cast_ne_zero.mpr F.denominator_ne_zero
  have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.numerator := by
    simpa [Int.castRingHom] using
      (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.numerator)
  apply Int.cast_injective (α := ℚ)
  rw [he, Int.cast_mul]
  have hh := (div_eq_iff hden).mp hy
  simpa only [mul_comm] using hh

end ClearedHistoryValue

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistorySubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Substitution constructs the actual rational expressions of a reversed history -/

namespace Ostmann.HistoryFormula

variable {σ τ : Type*}

@[simp] theorem value_prime (i : σ) (x : σ → ℚ) : (prime i).value x = x i :=
  ClearedHistoryValue.eval_variable i x

@[simp] theorem value_external (z : ℤ) (x : σ → ℚ) : (external z).value x = z :=
  ClearedHistoryValue.eval_constant z x

@[simp] theorem value_product (l r : HistoryFormula σ) (x : σ → ℚ) :
    (product l r).value x = l.value x * r.value x := by
  simp only [value, cleared, ClearedHistoryValue.eval_prod, Fintype.prod_bool,
    Bool.false_eq_true, ite_false, if_false, ite_true, if_true]

@[simp] theorem value_solve (l r : HistoryFormula σ) (v w s : ℤ) (hs : s ≠ 0) (x : σ → ℚ) :
    (solve l r v w s hs).value x = (v * r.value x - w * l.value x) / s :=
  ClearedHistoryValue.eval_pivot l.cleared r.cleared v w s hs x

theorem value_bind (F : HistoryFormula σ) (f : σ → HistoryFormula τ) (x : τ → ℚ) :
    (F.bind f).value x = F.value (fun i => (f i).value x) := by
  induction F with
  | prime i => simp only [bind, value_prime]
  | external z => simp only [bind, value_external]
  | product l r hl hr => simp only [bind, value_product, hl, hr]
  | solve l r v w s hs hl hr => simp only [bind, value_solve, hl, hr]

theorem value_listProduct (fs : List (HistoryFormula σ)) (x : σ → ℚ) :
    (listProduct fs).value x = (fs.map (fun F => F.value x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, value_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_IntegerHistoryReconstruction
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cleared formulas evaluate to the actual integer pivot reconstructions -/

namespace Ostmann

open scoped Classical

namespace HistoryPivotStep

variable {σ : Type*}

theorem formula_value (step : HistoryPivotStep σ) (x : σ → ℤ) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x : ℚ) / step.s := by
  have hp (l : List σ) : (l.map (fun i => (x i : ℚ))).prod = ((l.map x).prod : ℚ) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simp only [formula, HistoryFormula.value_solve, HistoryFormula.value_listProduct,
    List.map_map, Function.comp_def, HistoryFormula.value_prime, hp, numerator,
    Int.cast_sub, Int.cast_mul]

theorem formula_value_integer (step : HistoryPivotStep σ) (x : σ → ℤ) (hx : step.Valid x) :
    step.formula.value (fun i => (x i : ℚ)) = (step.numerator x / step.s : ℤ) := by
  rw [formula_value, Int.cast_div hx (Int.cast_ne_zero.mpr step.s_ne_zero)]

end HistoryPivotStep

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_ReconstructionIntegrality
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every original integer-divisibility gate is a cleared polynomial test -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.integralAt_iff {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.IntegralAt x ↔ F.cleared.denominator ∣
      MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, F.cleared.integer_value_cleared x y hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (div_eq_iff (Int.cast_ne_zero.mpr F.cleared.denominator_ne_zero)).mpr
    have he : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
      simpa [Int.castRingHom] using
        (MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator)
    rw [← he, hy, Int.cast_mul, mul_comm]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_HistoryFourierConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugated leaves use the same Fourier profile at the signed frequency -/

namespace Ostmann

open scoped FourierTransform SchwartzMap ComplexConjugate
open MeasureTheory

theorem real_schwartz_fourier_conj (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (t : ℝ) :
    conj (𝓕 ψ t) = 𝓕 ψ (-t) := by
  change conj (𝓕 (ψ : ℝ → ℂ) t) = 𝓕 (ψ : ℝ → ℂ) (-t)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, map_mul, hreal, ← Complex.exp_conj]
  congr 2
  norm_num [inner]
  exact Or.inl (map_natCast (starRingEnd ℂ) 2)

theorem normalizedFourierProfile_conj (ψ : ℝ → ℂ)
    (hψ : ∀ x, conj (ψ x) = ψ (-x)) (v z : ℝ) :
    conj (normalizedFourierProfile ψ v z) = normalizedFourierProfile ψ (-v) z := by
  simp only [normalizedFourierProfile, map_mul, Complex.conj_ofReal, hψ]
  congr 1
  congr 1
  ring

/-- The real physical smoothing function supplies the required symmetry;
there is no additional analytic hypothesis on the Fourier profile. -/
theorem normalizedFourierProfile_fourier_conj (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (v z : ℝ) :
    conj (normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v z) =
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (-v) z :=
  normalizedFourierProfile_conj (𝓕 ψ : 𝓢(ℝ, ℂ)) (real_schwartz_fourier_conj ψ hreal) v z

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferredPivotSubstitution
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Eliminating the extended integer by its exact signed quotient -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem reconstructedPivot_of_eq (N s : ℤ) (hs : s ≠ 0) (M : ℕ)
    (h : N = s * M) : reconstructedPivot N s = M := by
  rw [reconstructedPivot, Int.ediv_eq_of_eq_mul_right hs h, Int.toNat_natCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RecursiveTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with its actual reconstructed integer pivots -/

namespace Ostmann

open scoped BigOperators Classical

theorem ValidTransferNode.historyPivot_eq {State : Type*} {sys : TransferHistorySystem State}
    {σ : State} {s v w : ℤ} {P : ℕ} (h : ValidTransferNode sys σ s v w P) :
    historyPivot sys σ s v w = P :=
  reconstructedPivot_of_eq _ _ h.root_ne_zero P h.relation

/-- No witness choices enter the recursive weight: the integer equation
forces the pivot at every valid node. -/
theorem recursiveTransferWeight_node {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) (P : ℕ)
    (hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P) :
    recursiveTransferWeight sys leaf cutoff (n + 1) σ t =
      (cutoff σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) : ℂ) *
        recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 *
        star (recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2) := by
  simp only [recursiveTransferWeight, hP.historyPivot_eq, hP, ite_true, if_true]

theorem recursiveTransferWeight_nonzero_valid {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n σ t ≠ 0) :
    ValidTransferHistory sys n σ t := by
  induction n generalizing σ with
  | zero => trivial
  | succ n ih =>
    let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    by_cases hP : ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
    · rw [recursiveTransferWeight_node sys leaf cutoff n σ t P hP] at ht
      have hl : recursiveTransferWeight sys leaf cutoff n (sys.leftState σ P) t.2.1 ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul, ne_eq, not_true_eq_false] at ht
      have hr : recursiveTransferWeight sys leaf cutoff n (sys.rightState σ P) t.2.2 ≠ 0 := by
        intro hz
        simp only [hz, star_zero, mul_zero, ne_eq, not_true_eq_false] at ht
      exact ⟨P, hP, ih _ _ hl, ih _ _ hr⟩
    · exact False.elim (ht (by simp only [recursiveTransferWeight, P, hP, ite_false, if_false]))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveLeafExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact signed leaves and real support factor of a recursive history -/

namespace Ostmann

open scoped BigOperators ComplexConjugate SchwartzMap FourierTransform Classical

theorem signedLeafValue_flip {State : Type*} (F : State → ℤ → ℂ)
    (z : (State × ℤ) × Bool) :
    signedLeafValue F (z.1, !z.2) = conj (signedLeafValue F z) := by
  rcases z with ⟨⟨σ, v⟩, b⟩
  cases b <;> simp [signedLeafValue]

theorem signedLeafProduct_flip {State : Type*} (F : State → ℤ → ℂ)
    (l : List ((State × ℤ) × Bool)) :
    ((l.map (fun z => (z.1, !z.2))).map (signedLeafValue F)).prod =
      conj ((l.map (signedLeafValue F)).prod) := by
  induction l with
  | nil => simp
  | cons z l ih =>
    simp only [List.map_cons, List.prod_cons, signedLeafValue_flip, ih, map_mul]

/-- This equality uses the original recursive weight, including its actual
reconstructed pivots and its validity tests. -/
theorem recursiveTransferWeight_leaf_expansion {State : Type*}
    (sys : TransferHistorySystem State) (F : State → ℤ → ℂ)
    (leafCutoff : State → ℤ → ℝ) (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys (fun σ v => (leafCutoff σ v : ℂ) * F σ v) cutoff n σ t =
      (recursiveSupportFactor sys leafCutoff cutoff n σ t : ℂ) *
        ((transferLeafList sys n σ t).map (signedLeafValue F)).prod := by
  induction n generalizing σ with
  | zero => simp [recursiveTransferWeight, recursiveSupportFactor, transferLeafList, signedLeafValue]
  | succ n ih =>
    let v := frequencyRoot n t.2.1
    let w := frequencyRoot n t.2.2
    let P := historyPivot sys σ t.1 v w
    by_cases hp : ValidTransferNode sys σ t.1 v w P
    · rw [recursiveTransferWeight_node sys _ cutoff n σ t P hp]
      simp only [recursiveSupportFactor, transferLeafList, v, w, P, hp, ite_true, if_true,
        List.map_append, List.prod_append, signedLeafProduct_flip, ih, Complex.star_def, map_mul, Complex.conj_ofReal]
      push_cast
      ring
    · simp only [recursiveTransferWeight, recursiveSupportFactor, v, w, P, hp, ite_false, if_false,
        Complex.ofReal_zero, zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveNodeExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact preorder list of reconstructed arithmetic tests -/

namespace Ostmann

open scoped Classical

/-- The pivot witness in the original definition is precisely the integer
reconstruction, so no existential choice changes the child states. -/
theorem validTransferHistory_reconstructed_iff {State : Type*}
    (sys : TransferHistorySystem State) (n : ℕ) (σ : State) (t : FrequencyTree ℤ (n + 1)) :
    ValidTransferHistory sys (n + 1) σ t ↔
      let P := historyPivot sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      ValidTransferNode sys σ t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P ∧
        ValidTransferHistory sys n (sys.leftState σ P) t.2.1 ∧
        ValidTransferHistory sys n (sys.rightState σ P) t.2.2 := by
  constructor
  · rintro ⟨P, hp, hl, hr⟩
    rw [hp.historyPivot_eq]
    exact ⟨hp, hl, hr⟩
  · rintro ⟨hp, hl, hr⟩
    exact ⟨_, hp, hl, hr⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_RecursiveSupportExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All original range factors and all arithmetic tests in a flat history -/

namespace Ostmann

open scoped BigOperators Classical

theorem transferLeafCutoff_flip {State : Type*} (c : State → ℤ → ℝ)
    (l : List ((State × ℤ) × Bool)) :
    ((l.map (fun z => (z.1, !z.2))).map (transferLeafCutoff c)).prod =
      (l.map (transferLeafCutoff c)).prod := by
  simp only [List.map_map, Function.comp_def, transferLeafCutoff]
  rfl

/-- The support is exactly the product of original node and leaf cutoffs
on the original arithmetic validity set. -/
theorem recursiveSupportFactor_product {State : Type*}
    (sys : TransferHistorySystem State) (leafCutoff : State → ℤ → ℝ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (σ : State) (t : FrequencyTree ℤ n) :
    recursiveSupportFactor sys leafCutoff cutoff n σ t =
      if ValidTransferHistory sys n σ t then
        ((transferNodeList sys n σ t).map (transferNodeCutoff cutoff)).prod *
          ((transferLeafList sys n σ t).map (transferLeafCutoff leafCutoff)).prod
      else 0 := by
  induction n generalizing σ with
  | zero => simp [recursiveSupportFactor, ValidTransferHistory, transferNodeList,
      transferLeafList, transferLeafCutoff]
  | succ n ih =>
    rw [validTransferHistory_reconstructed_iff]
    simp only [recursiveSupportFactor, transferNodeList, transferLeafList,
      List.map_cons, List.prod_cons, List.map_append, List.prod_append,
      transferLeafCutoff_flip, transferNodeCutoff, ReconstructedTransferNode.pivot, ih]
    split_ifs <;> simp_all
    ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_BranchingHistoryReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

namespace BranchingWordHistory

variable {σ : Type*}

theorem wordFormula_value (word : List σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) :
    (HistoryFormula.listProduct (word.map env)).value a = ((word.map x).prod : ℚ) := by
  rw [HistoryFormula.value_listProduct, List.map_map]
  simp only [Function.comp_def]
  have hmap : word.map (fun i => (env i).value a) = word.map (fun i => (x i : ℚ)) := by
    apply List.map_congr_left
    intro i _
    exact he i
  rw [hmap]
  clear hmap
  induction word with
  | nil => simp
  | cons i word ih => simpa only [List.map_cons, List.prod_cons, Int.cast_mul] using congrArg (fun z => (x i : ℚ) * z) ih

theorem updatedFormulas_value (step : HistoryPivotStep σ) (env : σ → HistoryFormula σ)
    (a : σ → ℚ) (x : σ → ℤ) (he : ∀ i, (env i).value a = x i) (hx : step.Valid x) :
    ∀ i, (updatedFormulas step env i).value a = (step.applyInteger x i : ℚ) := by
  have hstep : (step.formula.bind env).value a = (step.numerator x / step.s : ℤ) := by
    rw [HistoryFormula.value_bind]
    have he' : (fun i => (env i).value a) = fun i => (x i : ℚ) := funext he
    rw [he']
    exact step.formula_value_integer x hx
  intro i
  by_cases hi : i = step.target
  · subst i
    simpa only [updatedFormulas, HistoryPivotStep.applyInteger, Function.update_self] using hstep
  · simpa only [updatedFormulas, HistoryPivotStep.applyInteger, Function.update_of_ne hi] using he i

end BranchingWordHistory
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete transfer system of word products and reconstructed pivots -/

namespace Ostmann

open scoped Classical

universe u

theorem wordTransferStep_numerator {σ : Type u} (d : WordTransferNode σ)
    (s v w : ℤ) (hs : s ≠ 0) (x : σ → ℕ) :
    (wordTransferStep d s v w hs).numerator (fun i => (x i : ℤ)) =
      v * ((d.right.map x).prod : ℤ) - w * ((d.left.map x).prod : ℤ) := by
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  simp only [HistoryPivotStep.numerator, wordTransferStep, hcast]

theorem wordTransferStep_valid {σ : Type u} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (x : σ → ℕ) (s v w : ℤ) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P) :
    (wordTransferStep d s v w hp.root_ne_zero).Valid (fun i => (x i : ℤ)) := by
  have hnum := wordTransferStep_numerator d s v w hp.root_ne_zero x
  change s ∣ (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ))
  rw [hnum]
  exact ⟨(P : ℤ), hp.relation⟩

theorem wordTransferStep_apply {σ : Type u} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (x : σ → ℕ) (s v w : ℤ) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P) :
    (wordTransferStep d s v w hp.root_ne_zero).applyInteger (fun i => (x i : ℤ)) =
      fun i => (Function.update x d.target P i : ℤ) := by
  have hnum : (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ)) = s * P := by
    rw [wordTransferStep_numerator]
    exact hp.relation
  funext i
  by_cases hi : i = d.target
  · subst i
    simp only [HistoryPivotStep.applyInteger,
      show (wordTransferStep d s v w hp.root_ne_zero).target = d.target from rfl, Function.update_self]
    change (wordTransferStep d s v w hp.root_ne_zero).numerator (fun i => (x i : ℤ)) / s = (P : ℤ)
    rw [hnum]
    exact Int.mul_ediv_cancel_left (P : ℤ) hp.root_ne_zero
  · simp only [HistoryPivotStep.applyInteger, wordTransferStep, Function.update_of_ne hi]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ReverseCopyMap
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reversing the literal copied-atom schedule

This construction is at the atom level: a current pivot group is one atom
carrying its total product. -/

namespace Ostmann

open scoped Classical

theorem reverseCopyLabelMap_copied {I σ : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (current : CopyScheduleAtoms role (n + 1) → σ)
    (i : CopyScheduleH role n) :
    reverseCopyLabelMap role n b pivot current ⟨i.val, i.property.1⟩ =
      current ⟨.inl (b, i.val), i.property⟩ := by
  simp only [reverseCopyLabelMap, i.property.2, dite_true]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduledTemplate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The atom schedule expanded into its actual prime constituents -/

namespace Ostmann

open scoped BigOperators Classical

theorem list_flatMap_product {α σ : Type*} (l : List α) (f : α → List σ) (x : σ → ℕ) :
    ((l.flatMap f).map x).prod = (l.map (fun a => ((f a).map x).prod)).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, List.map_append, List.prod_append, List.map_cons, List.prod_cons, ih]

theorem expandedHWord_product {I σ : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (current : CopyScheduleAtoms role (n + 1) → List σ) (x : σ → ℕ) :
    ((expandedHWord role n b current).map x).prod =
      ∏ i : CopyScheduleH role n, ((current ⟨.inl (b, i.val), i.property⟩).map x).prod := by
  rw [expandedHWord, list_flatMap_product]
  exact Finset.prod_map_toList _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleState
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Updating a fresh pivot coordinate performs the original atom reconstruction -/

namespace Ostmann

open scoped Classical

/-- Expose the child assignment with any decidable equality instance. -/
theorem wordTransferLeftState_node {σ : Type*} [DecidableEq σ] {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ) (P : ℕ) :
    (wordTransferSystem σ).leftState ((WordTransferTemplate.node d l r).state x) P =
      l.state (Function.update x d.target P) := by
  change (⟨n, l, _⟩ : WordTransferState σ) = ⟨n, l, _⟩
  congr 2
  funext i
  by_cases hi : i = d.target <;> simp only [Function.update_apply, hi, ite_true, if_true, ite_false, if_false]

theorem wordTransferRightState_node {σ : Type*} [DecidableEq σ] {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ) (P : ℕ) :
    (wordTransferSystem σ).rightState ((WordTransferTemplate.node d l r).state x) P =
      r.state (Function.update x d.target P) := by
  change (⟨n, r, _⟩ : WordTransferState σ) = ⟨n, r, _⟩
  congr 2
  funext i
  by_cases hi : i = d.target <;> simp only [Function.update_apply, hi, ite_true, if_true, ite_false, if_false]

theorem word_product_update_of_fresh {σ : Type*} [DecidableEq σ] (word : List σ) (x : σ → ℕ)
    (pivot : σ) (P : ℕ) (hfresh : ∀ i ∈ word, i ≠ pivot) :
    (word.map (Function.update x pivot P)).prod = (word.map x).prod := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact Function.update_of_ne (hfresh i hi) P x

/-- At the reconstructed pivot we read P, at H the selected copy, and at
Y the common retained value. This equality includes composite atom words. -/
theorem reverseCopyLabelMap_product_update {I σ : Type*} [DecidableEq σ] (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (pivot : σ) (P : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List σ) (x : σ → ℕ)
    (hfresh : ∀ i j, j ∈ current i → j ≠ pivot) (i : CopyScheduleAtoms role n) :
    ((reverseCopyLabelMap role n b [pivot] current i).map (Function.update x pivot P)).prod =
      reverseCopyLabelMap role n b P (fun j => ((current j).map x).prod) i := by
  unfold reverseCopyLabelMap
  split_ifs
  · exact word_product_update_of_fresh _ x pivot P (hfresh _)
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Function.update_self, mul_one]
  · exact word_product_update_of_fresh _ x pivot P (hfresh _)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fresh finite pivot coordinates for expanded prime-word templates -/

namespace Ostmann

open scoped Classical

theorem ExpandedCoordinateAfter.mono {α : Type*} {depth j k : ℕ}
    {v : ExpandedScheduledVariable α depth} (h : ExpandedCoordinateAfter k v) (hjk : j ≤ k) :
    ExpandedCoordinateAfter j v := by
  cases v with
  | inl a => trivial
  | inr p => exact hjk.trans h

theorem expandedPivotAddress_after (α : Type*) (depth j : ℕ) (hj : j ≤ depth) (path : List Bool) :
    ExpandedCoordinateAfter j (expandedPivotAddress α depth j path) := by
  change j ≤ j % (depth + 1)
  rw [Nat.mod_eq_of_lt (by omega)]

theorem expandedPivotAddress_fresh {α : Type*} {depth j : ℕ} (hj : j ≤ depth)
    (path : List Bool) (v : ExpandedScheduledVariable α depth)
    (hv : ExpandedCoordinateAfter (j + 1) v) : v ≠ expandedPivotAddress α depth j path := by
  intro he
  subst v
  change j + 1 ≤ j % (depth + 1) at hv
  rw [Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- Descending one level adds just its reconstructed pivot coordinate;
all inherited coordinates still lie strictly above the next pivot level. -/
theorem reverseExpandedCoordinates_after {I α : Type*} (role : I → CopyScheduleRole)
    (depth j : ℕ) (hj : j ≤ depth) (b : Bool) (path : List Bool)
    (current : CopyScheduleAtoms role (j + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter (j + 1) v) :
    ∀ i v, v ∈ reverseCopyLabelMap role j b [expandedPivotAddress α depth j path] current i →
      ExpandedCoordinateAfter j v := by
  intro i v hv
  unfold reverseCopyLabelMap at hv
  split_ifs at hv
  · exact (hc _ v hv).mono (by omega)
  · have he : v = expandedPivotAddress α depth j path := List.mem_singleton.mp hv
    rw [he]
    exact expandedPivotAddress_after α depth j hj path
  · exact (hc _ v hv).mono (by omega)

theorem expandedRootCoordinates_after {I α : Type*} (role : I → CopyScheduleRole)
    (depth : ℕ) (words : CopyScheduleAtoms role depth → List α) :
    ∀ i v, v ∈ (words i).map (Sum.inl : α → ExpandedScheduledVariable α depth) →
      ExpandedCoordinateAfter depth v := by
  intro i v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  trivial

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleAtomSystem
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal reverse transfer system on current atom values -/

namespace Ostmann

open scoped BigOperators Classical

theorem expanded_schedule_node_iff {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (path : List Bool) (current : CopyScheduleAtoms role (n + 1) → List σ)
    (x : σ → ℕ) (s v w : ℤ) (P : ℕ) :
    ValidTransferNode (wordTransferSystem σ)
      ((expandedScheduledTemplate role address childBound pivotBound (n + 1) path current).state x) s v w P ↔
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩ s v w P := by
  let wordState := (expandedScheduledTemplate role address childBound pivotBound (n + 1) path current).state x
  let atomState : ScheduleAtomState role := ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
  have hL : (wordTransferSystem σ).leftProduct wordState =
      (scheduleAtomSystem role childBound pivotBound).leftProduct atomState :=
    expandedHWord_product role n true current x
  have hR : (wordTransferSystem σ).rightProduct wordState =
      (scheduleAtomSystem role childBound pivotBound).rightProduct atomState :=
    expandedHWord_product role n false current x
  have hPB : (wordTransferSystem σ).pivotBound wordState =
      (scheduleAtomSystem role childBound pivotBound).pivotBound atomState := rfl
  have hCB : (wordTransferSystem σ).childBound wordState =
      (scheduleAtomSystem role childBound pivotBound).childBound atomState := rfl
  dsimp only [wordState, atomState] at hL hR hPB hCB
  constructor
  · intro h
    exact ⟨h.root_ne_zero, by simpa only [hR] using h.root_unit,
      by simpa only [hL, hR] using h.relation, h.pivot_pos, h.pivot_bound,
      h.left_bound, h.right_bound, by simpa only [hR, hPB, hCB] using h.range_gap, h.pivot_unit⟩
  · intro h
    exact ⟨h.root_ne_zero, by simpa only [hR] using h.root_unit,
      by simpa only [hL, hR] using h.relation, h.pivot_pos, h.pivot_bound,
      h.left_bound, h.right_bound, by simpa only [hR, hPB, hCB] using h.range_gap, h.pivot_unit⟩

/-- The inserted coordinate realizes exactly the original child atom state,
with composite atoms evaluated as their constituent prime products. -/
theorem expanded_schedule_child_state {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (hn : n ≤ depth) (b : Bool) (path : List Bool)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter (n + 1) v)
    (x : ExpandedScheduledVariable α depth → ℕ) (P : ℕ) :
    expandedAtomValues role n
      (reverseCopyLabelMap role n b [expandedPivotAddress α depth n path] current)
      (Function.update x (expandedPivotAddress α depth n path) P) =
      reverseCopyLabelMap role n b P (expandedAtomValues role (n + 1) current x) := by
  funext i
  unfold expandedAtomValues
  exact reverseCopyLabelMap_product_update role n b _ P current x
    (fun j v hv => expandedPivotAddress_fresh hn path v (hc j v hv)) i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleHistory
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The prime-word and atom systems have identical valid histories -/

namespace Ostmann

open scoped Classical

theorem expanded_schedule_history_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable α depth)) n
      ((expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current).state x) t ↔
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, expandedAtomValues role n current x⟩ t := by
  induction n generalizing path x with
  | zero => trivial
  | succ n ih =>
    have hn' : n ≤ depth := by omega
    change (∃ P, ValidTransferNode _ _ _ _ _ P ∧ _ ∧ _) ↔
      (∃ P, ValidTransferNode _ _ _ _ _ P ∧ _ ∧ _)
    apply exists_congr
    intro P
    apply and_congr (expanded_schedule_node_iff role (expandedPivotAddress α depth)
      childBound pivotBound n path current x _ _ _ P)
    apply and_congr
    · have he := expanded_schedule_child_state role depth n hn' true path current hc x P
      have hh := ih hn' (true :: path)
        (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' true path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
      rw [he] at hh
      rw [expandedScheduledTemplate, wordTransferLeftState_node]
      exact hh
    · have he := expanded_schedule_child_state role depth n hn' false path current hc x P
      have hh := ih hn' (false :: path)
        (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' false path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
      rw [he] at hh
      rw [expandedScheduledTemplate, wordTransferRightState_node]
      exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WeightedWordLeaves
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal frequency and polynomial of every reconstructed Fourier leaf -/

namespace Ostmann

open scoped Classical

theorem weightedWordLeaf_flip_evaluate {σ : Type*} (a : σ → ℚ) (l : List (WeightedWordLeaf σ)) :
    (l.map WeightedWordLeaf.flip).map (WeightedWordLeaf.evaluate a) =
      (l.map (WeightedWordLeaf.evaluate a)).map flipEvaluatedLeaf := by
  simp only [List.map_map]
  rfl

theorem evaluatedTransferLeaf_flip {σ : Type*} (l : List ((WordTransferState σ × ℤ) × Bool)) :
    (l.map (fun z => (z.1, !z.2))).map evaluatedTransferLeaf =
      (l.map evaluatedTransferLeaf).map flipEvaluatedLeaf := by
  simp only [List.map_map]
  rfl

theorem WordTransferTemplate.weightedLeaves_value {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) (a : σ → ℚ)
    (henv : ∀ i, (env i).value a = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (template.weightedLeaves t hn env).map (WeightedWordLeaf.evaluate a) =
      (transferLeafList (wordTransferSystem σ) n (template.state x) t).map evaluatedTransferLeaf := by
  induction template generalizing x env with
  | leaf word =>
    simp only [weightedLeaves, transferLeafList, List.map_cons, List.map_nil,
      WeightedWordLeaf.evaluate, evaluatedTransferLeaf, WordTransferTemplate.state, wordTransferLeafValue]
    congr 2
    apply congrArg (fun q : ℚ => (t, q))
    have he := BranchingWordHistory.wordFormula_value word env a (fun i => (x i : ℤ)) (by
      intro i
      simpa only [Int.cast_natCast] using henv i)
    rw [he]
    clear hv he
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, ih]
  | @node n d l r hl hr =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    have hs : step.Valid (fun i => (x i : ℤ)) :=
      wordTransferStep_valid d l r x _ _ _ P hp
    have he : step.applyInteger (fun i => (x i : ℤ)) = fun i => (Function.update x d.target P i : ℤ) :=
      wordTransferStep_apply d l r x _ _ _ P hp
    have hu := BranchingWordHistory.updatedFormulas_value step env a (fun i => (x i : ℤ))
      (by intro i; simpa only [Int.cast_natCast] using henv i) hs
    rw [he] at hu
    have hu' : ∀ i, (BranchingWordHistory.updatedFormulas step env i).value a =
        (Function.update x d.target P i : ℚ) := by
      intro i
      simpa only [Int.cast_natCast] using hu i
    simp only [weightedLeaves, transferLeafList, List.map_append,
      weightedWordLeaf_flip_evaluate, evaluatedTransferLeaf_flip]
    rw [hp.historyPivot_eq, hl _ _ _ _ hu' hvL, hr _ _ _ _ hu' hvR]
    rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact Fourier factors and polynomial budgets of a concrete word history -/

namespace Ostmann

open scoped SchwartzMap FourierTransform ComplexConjugate Classical

/-- Rational reconstruction and the real polynomial specialization agree,
including away from the integral support. -/
theorem HistoryFormula.realValue_ratCast {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) :
    F.realValue x = (F.value (fun i => (x i : ℚ)) : ℝ) := by
  have hr : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℝ) =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℝ) F.cleared.numerator
  have hq : (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator : ℚ) =
      MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun i => (x i : ℚ)) F.cleared.numerator := by
    simpa [Int.castRingHom] using
      MvPolynomial.map_eval₂Hom (RingHom.id ℤ) x (Int.castRingHom ℚ) F.cleared.numerator
  simp only [realValue, value, ClearedHistoryValue.eval, ← hr, ← hq,
    Rat.cast_div, Rat.cast_intCast]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact polynomial support of one original arithmetic transfer node -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.smallDivisionTest_of_value {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (y : ℤ)
    (hy : F.value (fun i => (x i : ℚ)) = y) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔ IsUnit (y : ZMod m) := by
  have he := F.cleared.integer_value_cleared x y hy
  simp only [smallDivisionTest, he, dvd_mul_right, true_and,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

theorem HistoryFormula.smallDivisionTest_iff {σ : Type*}
    (F : HistoryFormula σ) (x : σ → ℤ) (m : ℕ) :
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.cleared.numerator)
      F.cleared.denominator m ↔
      ∃ y : ℤ, F.value (fun i => (x i : ℚ)) = y ∧ IsUnit (y : ZMod m) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (F.integralAt_iff x).mpr h.1
    exact ⟨y, hy, (F.smallDivisionTest_of_value x y hy m).mp h⟩
  · rintro ⟨y, hy, hu⟩
    exact (F.smallDivisionTest_of_value x y hy m).mpr hu

/-- All original node conditions are represented: both coprimality tests,
integrality, positive bounded pivot, child-frequency bounds and strict gap. -/
theorem wordTransferGuard_iff {σ : Type*} {n : ℕ} (d : WordTransferNode σ)
    (l r : WordTransferTemplate σ n) (s v w : ℤ) (hs : s ≠ 0)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (wordTransferGuard d s v w hs env).ValidAt a ↔
      ∃ P, ValidTransferNode (wordTransferSystem σ)
        ((WordTransferTemplate.node d l r).state x) s v w P := by
  let step := wordTransferStep d s v w hs
  let f := step.formula.bind env
  let g := HistoryFormula.listProduct (d.right.map env)
  let R := (d.right.map x).prod
  let L := (d.left.map x).prod
  have hcast (word : List σ) : (word.map (fun i => (x i : ℤ))).prod = ((word.map x).prod : ℤ) := by
    induction word with
    | nil => rfl
    | cons i word ih => simp only [List.map_cons, List.prod_cons, Nat.cast_mul, ih]
  have hright : g.value (fun j => (a j : ℚ)) = (R : ℤ) := by
    have hh := BranchingWordHistory.wordFormula_value d.right env (fun j => (a j : ℚ))
      (fun i => (x i : ℤ)) (by intro i; simpa only [Int.cast_natCast] using henv i)
    have hc : (d.right.map (fun i => (x i : ℤ))).prod = (R : ℤ) := hcast d.right
    exact hh.trans (congrArg (fun z : ℤ => (z : ℚ)) hc)
  have hrightR : g.realValue a = (R : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hright, Rat.cast_intCast, Int.cast_natCast]
  have hf : f.value (fun j => (a j : ℚ)) = ((v * (R : ℤ) - w * (L : ℤ) : ℤ) : ℚ) / s := by
    rw [HistoryFormula.value_bind]
    have he : (fun i => (env i).value (fun j => (a j : ℚ))) = fun i => ((x i : ℤ) : ℚ) := by
      funext i; simpa only [Int.cast_natCast] using henv i
    rw [he, HistoryPivotStep.formula_value, wordTransferStep_numerator]
    rfl
  have hroot : IsUnit ((R : ℤ) : ZMod s.natAbs) ↔ IsCoprime s (R : ℤ) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime, Int.natCast_natAbs, IsCoprime.abs_left_iff]
  change (smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a f.cleared.numerator) f.cleared.denominator w.natAbs ∧
    smallDivisionTest (MvPolynomial.eval₂Hom (RingHom.id ℤ) a g.cleared.numerator) g.cleared.denominator s.natAbs ∧
    1 ≤ f.realValue a ∧ f.realValue a ≤ d.pivotBound ∧
    (2 * d.pivotBound * d.childBound : ℕ) < g.realValue a ∧
    v.natAbs ≤ d.childBound ∧ w.natAbs ≤ d.childBound) ↔ _
  rw [f.smallDivisionTest_iff, g.smallDivisionTest_of_value a (R : ℤ) hright,
    hrightR, hroot]
  constructor
  · rintro ⟨⟨Y, hY, hunit⟩, hcop, hlo, hhi, hgap, hv, hw⟩
    have hreal : f.realValue a = (Y : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hY, Rat.cast_intCast]
    rw [hreal] at hlo hhi
    have hY0 : 0 ≤ Y := by exact_mod_cast (show (0 : ℝ) ≤ Y by linarith)
    let P := Y.toNat
    have hPY : (P : ℤ) = Y := Int.toNat_of_nonneg hY0
    have hrel : v * (R : ℤ) - w * (L : ℤ) = s * P := by
      have he := (div_eq_iff (Int.cast_ne_zero.mpr hs)).mp (hf.symm.trans hY)
      have hi : v * (R : ℤ) - w * (L : ℤ) = Y * s := by exact_mod_cast he
      rw [hi, hPY, mul_comm]
    refine ⟨P, ⟨hs, hcop, hrel, ?_, ?_, hv, hw, ?_, ?_⟩⟩
    · have : (1 : ℤ) ≤ P := by rw [hPY]; exact_mod_cast hlo
      omega
    · have : (P : ℤ) ≤ d.pivotBound := by rw [hPY]; exact_mod_cast hhi
      exact_mod_cast this
    · exact_mod_cast hgap
    · have hu : IsUnit (P : ZMod w.natAbs) := by
        simpa only [← hPY, Int.cast_natCast] using hunit
      exact (ZMod.isUnit_iff_coprime P w.natAbs).mp hu
  · rintro ⟨P, hp⟩
    have hvalue : f.value (fun j => (a j : ℚ)) = (P : ℤ) := by
      have he : v * (R : ℤ) - w * (L : ℤ) = s * P := hp.relation
      rw [hf, he]
      push_cast
      exact mul_div_cancel_left₀ (P : ℚ) (Int.cast_ne_zero.mpr hs)
    have hreal : f.realValue a = (P : ℝ) := by
      rw [HistoryFormula.realValue_ratCast, hvalue, Rat.cast_intCast, Int.cast_natCast]
    refine ⟨⟨(P : ℤ), hvalue, ?_⟩, hp.root_unit, ?_, ?_, ?_, hp.left_bound, hp.right_bound⟩
    · simpa only [Int.cast_natCast] using (ZMod.isUnit_iff_coprime P w.natAbs).mpr hp.pivot_unit
    · rw [hreal]; exact_mod_cast hp.pivot_pos
    · rw [hreal]; exact_mod_cast hp.pivot_bound
    · exact_mod_cast hp.range_gap

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferGuardReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All branching support tests are the original recursive arithmetic support -/

namespace Ostmann

open scoped Classical

theorem wordTransferUpdatedFormulas_nat {σ : Type*} {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ)
    (s v w : ℤ) (hs : s ≠ 0) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P)
    (env : σ → HistoryFormula σ) (a : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    ∀ i, (BranchingWordHistory.updatedFormulas (wordTransferStep d s v w hs) env i).value
      (fun j => (a j : ℚ)) = (Function.update x d.target P i : ℚ) := by
  have hu := BranchingWordHistory.updatedFormulas_value (wordTransferStep d s v w hs)
    env (fun j => (a j : ℚ)) (fun i => (x i : ℤ))
    (by intro i; simpa only [Int.cast_natCast] using henv i)
    (wordTransferStep_valid d l r x s v w P hp)
  rw [wordTransferStep_apply d l r x s v w P hp] at hu
  intro i
  simpa only [Int.cast_natCast] using hu i

/-- The list contains precisely the original support conditions at every
node, including the independent substitutions on the two child branches. -/
theorem WordTransferTemplate.guards_iff {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ)
    (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (∀ g ∈ template.guards t hn env, g.ValidAt a) ↔
      ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  induction template generalizing env x with
  | leaf word => simp [guards, ValidTransferHistory]
  | @node n d l r hl hr =>
    let step := wordTransferStep d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1
    change (∀ g ∈ wordTransferGuard d t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hn.1 env ::
      (l.guards t.2.1 hn.2.1 (BranchingWordHistory.updatedFormulas step env) ++
        r.guards t.2.2 hn.2.2 (BranchingWordHistory.updatedFormulas step env)), g.ValidAt a) ↔ _
    simp only [List.mem_cons, List.mem_append, or_imp, forall_and, forall_eq]
    rw [wordTransferGuard_iff d l r _ _ _ hn.1 env a x henv]
    constructor
    · rintro ⟨⟨P, hp⟩, hL, hR⟩
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ hn.1 P hp env a henv
      exact ⟨P, hp, (hl _ _ _ _ hu).mp hL, (hr _ _ _ _ hu).mp hR⟩
    · rintro ⟨P, hp, hL, hR⟩
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ hn.1 P hp env a henv
      exact ⟨⟨P, hp⟩, (hl _ _ _ _ hu).mpr hL, (hr _ _ _ _ hu).mpr hR⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped Classical

theorem WordRange.toHistory_holds {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (r.toHistory env).Holds a ↔ r.Holds x := by
  have hval := BranchingWordHistory.wordFormula_value r.word env (fun j => (a j : ℚ))
    (fun i => (x i : ℤ)) (fun i => by simpa only [Int.cast_natCast] using henv i)
  have hprod : (r.word.map (fun i => (x i : ℤ))).prod = ((r.word.map x).prod : ℤ) := by
    induction r.word with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul]
  rw [hprod] at hval
  have hreal : (HistoryFormula.listProduct (r.word.map env)).realValue a = ((r.word.map x).prod : ℝ) := by
    rw [HistoryFormula.realValue_ratCast, hval, Rat.cast_intCast, Int.cast_natCast]
  exact Iff.of_eq (congrArg (fun z : ℝ => z ∈ Set.Icc r.lower r.upper) hreal)

/-- Every intermediate bin, including its endpoints, is precisely a range
of the formula obtained by the original integer reconstruction. -/
theorem WordRangeDecoration.formulas_iff {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (∀ r ∈ D.formulas template t ht env, r.Holds a) ↔ D.ValidAt template x t := by
  induction template generalizing env x with
  | leaf word =>
    cases D with
    | leaf ranges =>
      simp only [formulas, ValidAt, List.forall_mem_map]
      exact forall₂_congr fun r _ => r.toHistory_holds env a x henv
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ ht.1 P hp env a henv
      simp only [formulas, List.forall_mem_append, List.forall_mem_map, ValidAt, hp.historyPivot_eq]
      apply and_congr (forall₂_congr fun q _ => q.toHistory_holds env a x henv)
      apply and_congr
      · exact ihL L t.2.1 ht.2.1 _ _ hu hvL
      · exact ihR R t.2.2 ht.2.2 _ _ hu hvR

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleRanges
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom-product and word-bin ranges on the expanded schedule -/

namespace Ostmann

open scoped Classical

theorem ScheduleAtomRange.toWord_holds {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ) (x : σ → ℕ) :
    (r.toWord current).Holds x ↔ r.Holds (expandedAtomValues role n current x) := by
  unfold WordRange.Holds ScheduleAtomRange.Holds toWord
  rw [list_flatMap_product]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferArrays
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Indexed arrays of the actual branching guards and Fourier leaves -/

namespace Ostmann.WordTransferTemplate

open scoped Classical

variable {σ : Type*} {n : ℕ}

theorem guardAt_mem (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n - 1)) :
    template.guardAt t hn i ∈ template.guards t hn .prime := List.getElem_mem _

theorem guardAt_valid_iff (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (x : σ → ℕ) :
    (∀ i, (template.guardAt t hn i).ValidAt (fun j => (x j : ℤ))) ↔
      ValidTransferHistory (wordTransferSystem σ) n (template.state x) t := by
  rw [← template.guards_iff t hn .prime (fun j => (x j : ℤ)) x
    (by intro i; simp only [HistoryFormula.value_prime, Int.cast_natCast])]
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hg
    have hib : i < 2 ^ n - 1 := by rwa [template.guards_length] at hi
    exact h ⟨i, hib⟩
  · intro h i
    exact h _ (template.guardAt_mem t hn i)

end Ostmann.WordTransferTemplate

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferWeightIdentity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identification of the original recursive weight with its polynomial leaves -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem recursiveTransferWeight_flat {State : Type*} (sys : TransferHistorySystem State)
    (leaf : State → ℤ → ℂ) (n : ℕ) (x : State) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight sys leaf (fun _ _ _ _ => 1) n x t =
      if ValidTransferHistory sys n x t then
        ((transferLeafList sys n x t).map (signedLeafValue leaf)).prod else 0 := by
  have he := recursiveTransferWeight_leaf_expansion sys leaf (fun _ _ => 1) (fun _ _ _ _ => 1) n x t
  simp only [Complex.ofReal_one, one_mul] at he
  rw [recursiveSupportFactor_product] at he
  have hnode : transferNodeCutoff (fun (_ : State) (_ _ _ : ℤ) => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
  have hleaf : transferLeafCutoff (fun (_ : State) (_ : ℤ) => (1 : ℝ)) = fun _ => (1 : ℝ) := rfl
  rw [hnode, hleaf] at he
  simp only [List.map_const', List.prod_replicate, one_pow, mul_one] at he
  by_cases hv : ValidTransferHistory sys n x t
  · simpa only [hv, ite_true, if_true, Complex.ofReal_one, one_mul] using he
  · simpa only [hv, ite_false, if_false, Complex.ofReal_zero, zero_mul] using he

/-- Transport an arbitrary terminal factor through the actual frequency
and word-value reconstruction, retaining its conjugation flag. -/
theorem WordTransferTemplate.leaf_product_value {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t)
    (F : Bool → ℤ → ℝ → ℂ) :
    ((template.weightedLeaves t hn .prime).map (fun z =>
      F z.positive z.frequency (z.formula.realValue (fun i => (x i : ℤ))))).prod =
    ((transferLeafList (wordTransferSystem σ) n (template.state x) t).map (fun z =>
      F z.2 z.1.2 (wordTransferLeafValue z.1.1))).prod := by
  have he := template.weightedLeaves_value x t hn .prime (fun i => (x i : ℚ))
    (by intro i; simp only [HistoryFormula.value_prime]) hv
  have hh := congrArg (fun l => (l.map (fun z : Bool × ℤ × ℚ => F z.1 z.2.1 z.2.2)).prod) he
  simp only [List.map_map, Function.comp_def, WeightedWordLeaf.evaluate,
    evaluatedTransferLeaf, Rat.cast_natCast] at hh
  simpa only [HistoryFormula.realValue_ratCast, Int.cast_natCast] using hh

/-- The original weight with its terminal bins equals the constructed
polynomial coefficient on precisely its original arithmetic support. -/
theorem WordTransferTemplate.recursive_weight_polynomial_leaves {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ) :
    recursiveTransferWeight (wordTransferSystem σ)
      (fun τ v => (if (wordTransferLeafValue τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((wordTransferLeafValue τ : ℝ) / X))
      (fun _ _ _ _ => 1) n (template.state x) t =
      if ValidTransferHistory (wordTransferSystem σ) n (template.state x) t then
        polynomialLeafProduct (template.weightedLeaves t hn .prime) (𝓕 ψ : 𝓢(ℝ, ℂ))
          X lo hi (fun i => (x i : ℤ)) else 0 := by
  rw [recursiveTransferWeight_flat]
  split_ifs with hv
  · rw [polynomialLeafProduct, template.leaf_product_value x t hn hv
      (fun b v r => (if r / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) (if b then (v : ℝ) else -(v : ℝ)) (r / X))]
    apply congrArg List.prod
    apply List.map_congr_left
    intro z _
    rcases z with ⟨⟨τ, v⟩, flag⟩
    cases flag
    · simp only [signedLeafValue, Bool.false_eq_true, ite_false, if_false, map_mul]
      rw [normalizedFourierProfile_fourier_conj ψ hreal]
      split_ifs <;> simp
    · rfl
  · rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordTransferUniformCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original bounded-bin recursive weight is the constructed coefficient -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem list_prod_complex_gate {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P] (F : α → ℂ) :
    (l.map (fun a => (if P a then (1 : ℂ) else 0) * F a)).prod =
      (if ∀ a ∈ l, P a then 1 else 0) * (l.map F).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.mem_cons, forall_eq_or_imp]
    split_ifs <;> simp_all

theorem list_prod_getElem_of_length {α : Type*} (l : List α) (m : ℕ) (hl : l.length = m)
    (F : α → ℂ) :
    (l.map F).prod = ∏ i : Fin m, F (l[i.val]'(by rw [hl]; exact i.isLt)) := by
  subst m
  exact (Fin.prod_univ_fun_getElem l F).symm

theorem list_forall_getElem_of_length {α : Type*} (l : List α) (m : ℕ) (hl : l.length = m)
    (P : α → Prop) :
    (∀ a ∈ l, P a) ↔ ∀ i : Fin m, P (l[i.val]'(by rw [hl]; exact i.isLt)) := by
  constructor
  · intro h i
    exact h _ (List.getElem_mem _)
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hm : i < m := by rwa [hl] at hi
    exact h ⟨i, hm⟩

theorem polynomialLeafProduct_indexed {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (ψ : ℝ → ℂ) (X lo hi : ℝ) (x : σ → ℤ) :
    polynomialLeafProduct (template.weightedLeaves t hn .prime) ψ X lo hi x =
      (if ∀ i, (template.leafAt t hn i).formula.realValue x / X ∈ Set.Icc lo hi then 1 else 0) *
        ∏ i, normalizedFourierProfile ψ
          (if (template.leafAt t hn i).positive then ((template.leafAt t hn i).frequency : ℝ)
            else -((template.leafAt t hn i).frequency : ℝ))
          ((template.leafAt t hn i).formula.realValue x / X) := by
  rw [polynomialLeafProduct, list_prod_complex_gate (template.weightedLeaves t hn .prime)
    (fun z : WeightedWordLeaf σ => z.formula.realValue x / X ∈ Set.Icc lo hi)
    (fun z => normalizedFourierProfile ψ (if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ))
      (z.formula.realValue x / X))]
  simp only [list_forall_getElem_of_length _ (2 ^ n) (template.weightedLeaves_length t hn .prime)]
  rw [list_prod_getElem_of_length _ (2 ^ n) (template.weightedLeaves_length t hn .prime)]
  rfl

/-- This equality derives the coefficient on natural assignments from its support
and Fourier reconstruction. -/
theorem WordFourierParameters.uniform_coefficient {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t) (profile : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (x : σ → ℕ) :
    (WordFourierParameters.uniform n profile X lo hi hlo hhi).coefficient
      template t hn (fun i => (x i : ℤ)) =
      if ValidTransferHistory (wordTransferSystem σ) n (template.state x) t then
        polynomialLeafProduct (template.weightedLeaves t hn .prime) profile X lo hi (fun i => (x i : ℤ))
      else 0 := by
  rw [polynomialLeafProduct_indexed]
  simp only [coefficient, uniform, frequency, template.guardAt_valid_iff t hn x]
  split_ifs <;> simp_all

/-- Exact identification with the weight used in the original amplitude. -/
theorem WordTransferTemplate.recursive_weight_coefficient {σ : Type*} {n : ℕ}
    (template : WordTransferTemplate σ n) (x : σ → ℕ) (t : FrequencyTree ℤ n)
    (hn : NonzeroInternalFrequencies n t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    recursiveTransferWeight (wordTransferSystem σ)
      (fun τ v => (if (wordTransferLeafValue τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((wordTransferLeafValue τ : ℝ) / X))
      (fun _ _ _ _ => 1) n (template.state x) t =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).coefficient
        template t hn (fun i => (x i : ℤ)) := by
  rw [WordFourierParameters.uniform_coefficient,
    template.recursive_weight_polynomial_leaves x t hn ψ hreal X lo hi]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRangeWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The recursive weight with every intermediate range retained -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

theorem WordRangeDecoration.weight_eq {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (leaf : WordTransferState σ → ℤ → ℂ) (x : σ → ℕ) (t : FrequencyTree ℤ n) :
    D.weight leaf template x t =
      (if D.ValidAt template x t then 1 else 0) *
        recursiveTransferWeight (wordTransferSystem σ) leaf (fun _ _ _ _ => 1) n (template.state x) t := by
  induction template generalizing x with
  | leaf word =>
    cases D
    simp only [weight, ValidAt, recursiveTransferWeight]
    congr 1
    congr 1
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      let P := historyPivot (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
        t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
      by_cases hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x)
          t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) P
      · rw [recursiveTransferWeight_node _ _ _ n _ t P hp]
        simp only [weight, ValidAt, hp, ite_true, if_true, P, ihL, ihR, Complex.ofReal_one, one_mul,
          wordTransferLeftState_node, wordTransferRightState_node]
        split_ifs <;> simp_all
      · simp only [weight, recursiveTransferWeight, P, hp, ite_false, if_false, mul_zero]

/-- The polynomial range coefficient is the literal recursive weight with
all bins at every node, not a replacement support assumption. -/
theorem WordRangeDecoration.weight_coefficient {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (x : σ → ℕ) (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) :
    D.weight
      (fun τ v => (if (wordTransferLeafValue τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((wordTransferLeafValue τ : ℝ) / X))
      template x t =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).rangedCoefficient
        D template t ht (fun i => (x i : ℤ)) := by
  rw [weight_eq, template.recursive_weight_coefficient x t ht ψ hreal X lo hi hlo hhi,
    WordFourierParameters.rangedCoefficient]
  by_cases hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t
  · have he := D.formulas_iff template t ht .prime (fun i => (x i : ℤ)) x
      (fun i => by simp only [HistoryFormula.value_prime, Int.cast_natCast]) hv
    simp only [he]
  · rw [WordFourierParameters.uniform_coefficient]
    simp only [hv, ite_false, if_false, mul_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedRangeReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original atom ranges are exactly the replayed prime-word tests -/

namespace Ostmann

open scoped Classical

theorem expanded_schedule_pivot_eq {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ)
    (childBound pivotBound : ℕ → ℕ) (n : ℕ) (path : List Bool)
    (current : CopyScheduleAtoms role (n + 1) → List σ) (x : σ → ℕ) (s v w : ℤ) :
    historyPivot (wordTransferSystem σ)
      ((expandedScheduledTemplate role address childBound pivotBound (n + 1) path current).state x) s v w =
    historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩ s v w := by
  simp only [historyPivot, expandedScheduledTemplate, WordTransferTemplate.state,
    wordTransferSystem, wordTransferLeft, wordTransferRight, expandedHWord_product,
    scheduleAtomSystem, scheduleAtomLeft, scheduleAtomRight, expandedAtomValues]

theorem expandedScheduleRanges_valid_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    (expandedScheduleRanges role (expandedPivotAddress α depth) ranges n path current).ValidAt
        (expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current) x t ↔
      scheduleAtomRangesValid role childBound pivotBound ranges n (expandedAtomValues role n current x) t := by
  induction n generalizing path x with
  | zero =>
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.ValidAt,
      scheduleAtomRangesValid, List.forall_mem_map]
    exact forall₂_congr fun r _ => r.toWord_holds current x
  | succ n ih =>
    let P := historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hn' : n ≤ depth := by omega
    have hL := ih hn' (true :: path)
      (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' true path current hc)
      (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
    have hR := ih hn' (false :: path)
      (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' false path current hc)
      (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
    rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hL
    rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hR
    have hp := expanded_schedule_pivot_eq role (expandedPivotAddress α depth)
      childBound pivotBound n path current x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    dsimp only [expandedScheduledTemplate] at hp
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.ValidAt,
      hp, scheduleAtomRangesValid, List.forall_mem_map]
    apply and_congr (forall₂_congr fun r _ => r.toWord_holds current x)
    apply and_congr
    · convert hL using 2
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _
    · convert hR using 2
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedScheduleWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original atom weight is the concrete prime-word coefficient -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform ComplexConjugate

theorem expanded_schedule_leaf_total {I σ : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (address : ℕ → List Bool → σ) (childBound pivotBound : ℕ → ℕ)
    (path : List Bool) (current : CopyScheduleAtoms role 0 → List σ) (x : σ → ℕ) :
    wordTransferLeafValue
      ((expandedScheduledTemplate role address childBound pivotBound 0 path current).state x) =
      scheduleAtomTotal role ⟨0, expandedAtomValues role 0 current x⟩ := by
  change ((Finset.univ.toList.flatMap current).map x).prod = _
  rw [list_flatMap_product]
  exact Finset.prod_map_toList _ _

theorem recursiveTransferWeight_eq_zero_of_not_valid {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (h : ¬ ValidTransferHistory sys n x t) :
    recursiveTransferWeight sys leaf cutoff n x t = 0 := by
  by_contra hn
  exact h (recursiveTransferWeight_nonzero_valid sys leaf cutoff n x t hn)

/-- Expanding the constituents preserves the whole recursive weight,
including invalid support, the forced pivots and all right conjugations. -/
theorem expanded_schedule_weight_eq {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (F : ℕ → ℤ → ℂ) (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (wordTransferSystem (ExpandedScheduledVariable α depth))
      (fun τ v => F (wordTransferLeafValue τ) v) (fun _ _ _ _ => 1) n
      ((expandedScheduledTemplate role (expandedPivotAddress α depth)
        childBound pivotBound n path current).state x) t =
    recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
      (fun τ v => F (scheduleAtomTotal role τ) v) (fun _ _ _ _ => 1) n
      ⟨n, expandedAtomValues role n current x⟩ t := by
  induction n generalizing path x with
  | zero =>
    change F _ t = F _ t
    rw [expanded_schedule_leaf_total]
  | succ n ih =>
    by_cases hv : ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable α depth)) (n + 1)
        ((expandedScheduledTemplate role (expandedPivotAddress α depth)
          childBound pivotBound (n + 1) path current).state x) t
    · obtain ⟨P, hp, _, _⟩ := hv
      have hpa := (expanded_schedule_node_iff role (expandedPivotAddress α depth)
        childBound pivotBound n path current x _ _ _ P).mp hp
      rw [recursiveTransferWeight_node _ _ _ _ _ _ P hp,
        recursiveTransferWeight_node _ _ _ _ _ _ P hpa]
      have hn' : n ≤ depth := by omega
      have hl := ih hn' (true :: path)
        (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' true path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
      have hr := ih hn' (false :: path)
        (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
        (reverseExpandedCoordinates_after role depth n hn' false path current hc)
        (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
      rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hl
      rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hr
      simp only [expandedScheduledTemplate, wordTransferLeftState_node, wordTransferRightState_node]
      rw [hl, hr]
      rfl
    · have hva := mt (expanded_schedule_history_iff role childBound pivotBound depth (n + 1)
          hn path current hc x t).mpr hv
      rw [recursiveTransferWeight_eq_zero_of_not_valid _ _ _ _ _ _ hv,
        recursiveTransferWeight_eq_zero_of_not_valid _ _ _ _ _ _ hva]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedScheduleCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original grouped-atom amplitudes in the independent prime variables -/

namespace Ostmann

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem expandedPrimeNatValues_cast {V : Type*} (n : ℕ) (x : V → ℕ) :
    (fun i => (expandedPrimeNatValues n x i : ℤ)) =
      expandedPrimeValues n (fun i => (x i : ℤ)) := by
  funext i
  cases i <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedRangedWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original all-stage ranges in the concrete Fourier coefficient -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem expanded_schedule_ranged_weight_eq {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n)) (F : ℕ → ℤ → ℂ)
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    (expandedScheduleRanges role (expandedPivotAddress α depth) ranges n path current).weight
      (fun τ v => F (wordTransferLeafValue τ) v)
      (expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current) x t =
      (if scheduleAtomRangesValid role childBound pivotBound ranges n (expandedAtomValues role n current x) t
        then 1 else 0) *
      recursiveTransferWeight (scheduleAtomSystem role childBound pivotBound)
        (fun τ v => F (scheduleAtomTotal role τ) v) (fun _ _ _ _ => 1) n
        ⟨n, expandedAtomValues role n current x⟩ t := by
  rw [WordRangeDecoration.weight_eq,
    expanded_schedule_weight_eq role childBound pivotBound F depth n hn path current hc x t]
  have he := expandedScheduleRanges_valid_iff role childBound pivotBound ranges depth n hn path current hc x t
  simp only [he]

/-- The actual grouped-atom weight with all intermediate product and word
bins is the coefficient used by the ranged one-sided bound. -/
theorem groupedRangedFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).rangedCoefficient
        (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
        t ht (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  let F : ℕ → ℤ → ℂ := fun M v => (if (M : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
    normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((M : ℝ) / X)
  have he := expanded_schedule_ranged_weight_eq role childBound pivotBound ranges F n n le_rfl []
    (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role n words)
    (expandedPrimeNatValues n x) t
  have hx : expandedAtomValues role n (fun i => (words i).map Sum.inl) (expandedPrimeNatValues n x) =
      fun i => ((words i).map x).prod := by
    funext i
    unfold expandedAtomValues
    rw [List.map_map]
    rfl
  rw [hx] at he
  have hw := (expandedRootRanges role n words ranges).weight_coefficient
    (expandedRootTemplate role n words childBound pivotBound) (expandedPrimeNatValues n x)
    t ht ψ hreal X lo hi hlo hhi
  rw [expandedPrimeNatValues_cast] at hw
  exact he.symm.trans hw

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inherited frequency-unit tests along the actual word reconstruction -/

namespace Ostmann

open scoped Classical

theorem WordRange.toUnitGuard_holds {σ : Type*} (r : WordRange σ)
    (env : σ → HistoryFormula σ) (s : ℤ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    (r.toUnitGuard env s).Holds a ↔ ((r.word.map x).prod).Coprime s.natAbs := by
  have hval := BranchingWordHistory.wordFormula_value r.word env (fun j => (a j : ℚ))
    (fun i => (x i : ℤ)) (fun i => by simpa only [Int.cast_natCast] using henv i)
  have hprod : (r.word.map (fun i => (x i : ℤ))).prod = ((r.word.map x).prod : ℤ) := by
    induction r.word with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons, List.prod_cons, ih, Nat.cast_mul]
  rw [hprod] at hval
  change smallDivisionTest
    (MvPolynomial.eval₂Hom (RingHom.id ℤ) a (r.toHistory env).formula.cleared.numerator)
    (r.toHistory env).formula.cleared.denominator s.natAbs ↔ _
  dsimp only [WordRange.toHistory]
  rw [HistoryFormula.smallDivisionTest_of_value _ a _ hval s.natAbs]
  simpa only [Int.cast_natCast] using ZMod.isUnit_iff_coprime (r.word.map x).prod s.natAbs

/-- The quotient residues retain every inherited frequency-unit condition,
including at terminal leaves and at previously reconstructed pivots. -/
theorem WordRangeDecoration.unitGuards_iff {σ : Type*} {n : ℕ}
    (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (∀ g ∈ D.unitGuards template t ht env, g.Holds a) ↔ D.UnitsAt template x t := by
  induction template generalizing env x with
  | leaf word =>
    cases D with
    | leaf ranges =>
      simp only [unitGuards, UnitsAt, List.forall_mem_map]
      exact forall₂_congr fun r _ => r.toUnitGuard_holds env t a x henv
  | @node n d l r ihL ihR =>
    cases D with
    | node ranges L R =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ ht.1 P hp env a henv
      simp only [unitGuards, List.forall_mem_append, List.forall_mem_map, UnitsAt, hp.historyPivot_eq]
      apply and_congr (forall₂_congr fun q _ => q.toUnitGuard_holds env t.1 a x henv)
      exact and_congr (ihL L t.2.1 ht.2.1 _ _ hu hvL) (ihR R t.2.2 ht.2.2 _ _ hu hvR)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordUnitCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact residue support for all inherited word units -/

namespace Ostmann

open scoped Classical

namespace WordFourierParameters

/-- On valid natural histories these are exactly the recursively inherited
unit conditions, including the original leaf-frequency conditions. -/
theorem unitRangedCoefficient_nat {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    p.unitRangedCoefficient U D template t ht (fun i => (x i : ℤ)) =
      (if U.UnitsAt template x t then 1 else 0) *
        p.rangedCoefficient D template t ht (fun i => (x i : ℤ)) := by
  unfold unitRangedCoefficient
  have he := U.unitGuards_iff template t ht .prime (fun i => (x i : ℤ)) x
    (fun i => by simp only [HistoryFormula.value_prime, Int.cast_natCast]) hv
  simp only [he]

theorem coefficient_eq_zero_of_not_valid {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (template : WordTransferTemplate σ n) (t : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ)
    (hv : ¬ ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    p.coefficient template t ht (fun i => (x i : ℤ)) = 0 := by
  unfold coefficient
  split_ifs with h
  · exact False.elim (hv ((template.guardAt_valid_iff t ht x).mp h.1))
  · exact zero_mul _

theorem unitRangedCoefficient_nat_all {σ : Type*} {n : ℕ} (p : WordFourierParameters n)
    (U D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : σ → ℕ) :
    p.unitRangedCoefficient U D template t ht (fun i => (x i : ℤ)) =
      (if U.UnitsAt template x t then 1 else 0) *
        p.rangedCoefficient D template t ht (fun i => (x i : ℤ)) := by
  by_cases hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t
  · exact p.unitRangedCoefficient_nat U D template t ht x hv
  · simp only [unitRangedCoefficient, rangedCoefficient,
      p.coefficient_eq_zero_of_not_valid template t ht x hv, mul_zero]

end WordFourierParameters

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedUnitReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original atom frequency-units on the expanded prime-word schedule -/

namespace Ostmann

open scoped Classical

theorem ScheduleAtomRange.toWord_coprime {I σ : Type*} {role : I → CopyScheduleRole} {n : ℕ}
    (r : ScheduleAtomRange role n) (current : CopyScheduleAtoms role n → List σ) (x : σ → ℕ) (m : ℕ) :
    (((r.toWord current).word.map x).prod).Coprime m ↔
      ((r.atoms.map (expandedAtomValues role n current x)).prod).Coprime m := by
  change (((r.atoms.flatMap current).map x).prod).Coprime m ↔ _
  rw [list_flatMap_product]
  rfl

theorem expandedScheduleUnits_valid_iff {I α : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (n : ℕ) → List (ScheduleAtomRange role n))
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable α depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (x : ExpandedScheduledVariable α depth → ℕ) (t : FrequencyTree ℤ n) :
    (expandedScheduleRanges role (expandedPivotAddress α depth) ranges n path current).UnitsAt
        (expandedScheduledTemplate role (expandedPivotAddress α depth) childBound pivotBound n path current) x t ↔
      scheduleAtomUnitsValid role childBound pivotBound ranges n (expandedAtomValues role n current x) t := by
  induction n generalizing path x with
  | zero =>
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.UnitsAt,
      scheduleAtomUnitsValid, List.forall_mem_map]
    exact forall₂_congr fun r _ => r.toWord_coprime current x t.natAbs
  | succ n ih =>
    let P := historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hn' : n ≤ depth := by omega
    have hL := ih hn' (true :: path)
      (reverseCopyLabelMap role n true [expandedPivotAddress α depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' true path current hc)
      (Function.update x (expandedPivotAddress α depth n path) P) t.2.1
    have hR := ih hn' (false :: path)
      (reverseCopyLabelMap role n false [expandedPivotAddress α depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' false path current hc)
      (Function.update x (expandedPivotAddress α depth n path) P) t.2.2
    rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hL
    rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hR
    have hp := expanded_schedule_pivot_eq role (expandedPivotAddress α depth)
      childBound pivotBound n path current x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    dsimp only [expandedScheduledTemplate] at hp
    simp only [expandedScheduleRanges, expandedScheduledTemplate, WordRangeDecoration.UnitsAt,
      hp, scheduleAtomUnitsValid, List.forall_mem_map]
    apply and_congr (forall₂_congr fun r _ => r.toWord_coprime current x t.1.natAbs)
    apply and_congr
    · convert hL using 2
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _
    · convert hR using 2
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Arithmetic_TotalAtomUnits
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unit condition on every current atom at every frequency -/

namespace Ostmann

open scoped BigOperators Classical

/-- A unit product is exactly the original assertion that every current
atom is a unit. The dummy interval endpoints play no part in this test. -/
theorem totalAtomUnitRanges_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (s : ℤ) :
    (∀ r ∈ totalAtomUnitRanges role n, ((r.atoms.map x).prod).Coprime s.natAbs) ↔
      ∀ i, (x i).Coprime s.natAbs := by
  simp only [totalAtomUnitRanges, List.mem_singleton, forall_eq]
  rw [Finset.prod_map_toList]
  exact Nat.coprime_fintype_prod_left_iff

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_AtomTopSupport
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The top atom support as explicit original-prime tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem atomPairChecks_iff {I V : Type*} [Fintype I]
    (words : I → List V) (x : V → ℕ) :
    (∀ c ∈ atomPairChecks words, c.Holds x) ↔
      Pairwise (fun i j => ((words i).map x).prod.Coprime ((words j).map x).prod) := by
  constructor
  · intro h i j hij
    rw [Nat.coprime_list_prod_left_iff]
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    rw [Nat.coprime_list_prod_right_iff]
    intro b hb
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
    apply h (.distinct v w)
    apply List.mem_flatMap.mpr
    refine ⟨i, by simp, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, by simp, ?_⟩
    rw [ite_eq_right hij]
    exact List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  · intro h c hc
    obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
    by_cases hij : i = j
    · simp only [hij, ite_true, if_true, List.not_mem_nil] at hc
    · rw [ite_eq_right hij] at hc
      obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
      have hh : ((words i).map x).prod.Coprime ((words j).map x).prod := h hij
      rw [Nat.coprime_list_prod_left_iff] at hh
      have hh' := hh _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
      rw [Nat.coprime_list_prod_right_iff] at hh'
      exact hh' _ (List.mem_map.mpr ⟨w, hw, rfl⟩)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedOutsideCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every outside coordinate is an original prime coordinate -/

namespace Ostmann

open scoped Classical

theorem copyScheduleY_not_pivot {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (i : CopyScheduleY role n) (k : ℕ) : copyScheduleRole role n i.val ≠ .pivot k := by
  intro hk
  have hn := (surviving_pivot_is_positive role n k i.val i.property.1 hk).1
  have hc := i.property.2.1
  have he := i.property.2.2
  rw [hk] at hc he
  simp only [CopyScheduleRole.copiedAt, decide_eq_false_iff_not, CopyScheduleRole.erasedAt] at hc he
  omega

/-- Reversing a step inserts an integer only at the erased active pivot;
all other role types retain actual-prime words. -/
theorem reverseExpandedActualCoordinates {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (b : Bool) (pivot : ExpandedScheduledVariable α depth)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current) :
    ExpandedActualCoordinates role depth n (reverseCopyLabelMap role n b [pivot] current) := by
  intro i hi v hv
  unfold reverseCopyLabelMap at hv
  split_ifs at hv with hcopy herase
  · apply hc _ _ v hv
    intro k hk
    change (copyScheduleRole role n i.val).afterCopy b = .pivot k at hk
    exact hi k ((CopyScheduleRole.afterCopy_eq_pivot _ b k).mp hk).2
  · have he := herase
    cases hr : copyScheduleRole role n i.val <;>
      simp only [hr, CopyScheduleRole.erasedAt, Bool.false_eq_true] at he
    rename_i k
    exact False.elim (hi k hr)
  · apply hc _ ?_ v hv
    intro k hk
    exact hi k hk

theorem expandedRoot_actual_coordinates {I α : Type*} (role : I → CopyScheduleRole)
    (depth : ℕ) (words : CopyScheduleAtoms role depth → List α) :
    ExpandedActualCoordinates role depth depth (fun i => (words i).map Sum.inl) := by
  intro i _ v hv
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
  exact ⟨a, rfl⟩

/-- Thus every constituent of Y is an actual prime variable even after
ancestor pivots have already been reconstructed. -/
theorem expandedYWord_actual {I α : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable α depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (i : CopyScheduleY role n) :
    ∀ v ∈ current ⟨.inr i.val, i.property⟩, ∃ a : α, v = .inl a := by
  apply hc
  exact fun k => copyScheduleY_not_pivot role n i k

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedOutsideWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original prime constituents of each retained Y atom -/

namespace Ostmann

open scoped Classical

theorem expandedOriginalWord_exact {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth))
    (hw : ∀ v ∈ w, ∃ a : V, v = .inl a) :
    (expandedOriginalWord w).map Sum.inl = w := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    obtain ⟨a, rfl⟩ := hw v (by simp)
    simp only [expandedOriginalWord, List.map_cons]
    rw [ih (fun v hv => hw v (by simp only [List.mem_cons]; exact Or.inr hv))]

theorem expandedOriginalWord_values {V : Type*} {depth : ℕ} {β : Type*}
    (w : List (ExpandedScheduledVariable V depth))
    (hw : ∀ v ∈ w, ∃ a : V, v = .inl a)
    (x : ExpandedScheduledVariable V depth → β) :
    (expandedOriginalWord w).map (fun a => x (.inl a)) = w.map x := by
  calc
    _ = ((expandedOriginalWord w).map Sum.inl).map x := (List.map_map ..).symm
    _ = _ := congrArg (List.map x) (expandedOriginalWord_exact w hw)

theorem expandedYPrimeWord_values {I V β : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (i : CopyScheduleY role n) (x : ExpandedScheduledVariable V depth → β) :
    (expandedYPrimeWord role depth n current i).map (fun a => x (.inl a)) =
      (current ⟨.inr i.val, i.property⟩).map x :=
  expandedOriginalWord_values _ (expandedYWord_actual role depth n current hc i) x

theorem expandedYPrimeWord_product {I V : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (i : CopyScheduleY role n) (x : ExpandedScheduledVariable V depth → ℕ) :
    ((expandedYPrimeWord role depth n current i).map (fun a => x (.inl a))).prod =
      expandedAtomValues role (n + 1) current x ⟨.inr i.val, i.property⟩ := by
  rw [expandedYPrimeWord_values role depth n current hc i x]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordPrimeReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replaying the large-prime coprimalities at every reconstructed pivot -/

namespace Ostmann

open scoped Classical

theorem HistoryFormula.integerValue_of_value {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℤ) (y : ℤ) (hy : F.value (fun i => (a i : ℚ)) = y) :
    F.integerValue a = y := by
  unfold integerValue
  rw [F.cleared.integer_value_cleared a y hy,
    Int.mul_ediv_cancel_left _ F.cleared.denominator_ne_zero]

theorem wordTransfer_pivot_formula_value {σ : Type*} {n : ℕ}
    (d : WordTransferNode σ) (l r : WordTransferTemplate σ n) (x : σ → ℕ)
    (s v w : ℤ) (hs : s ≠ 0) (P : ℕ)
    (hp : ValidTransferNode (wordTransferSystem σ) ((WordTransferTemplate.node d l r).state x) s v w P)
    (env : σ → HistoryFormula σ) (a : σ → ℤ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ)) :
    ((wordTransferStep d s v w hs).formula.bind env).value (fun j => (a j : ℚ)) = (P : ℤ) := by
  have h := wordTransferUpdatedFormulas_nat d l r x s v w hs P hp env a henv d.target
  simpa only [BranchingWordHistory.updatedFormulas, wordTransferStep, Function.update_self,
    Int.cast_natCast] using h

/-- The tests use original prime values, unchanged by the pivot updates. -/
theorem WordPrimeDecoration.checks_iff {σ V : Type*} {n : ℕ}
    (D : WordPrimeDecoration V n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (env : σ → HistoryFormula σ) (a : σ → ℤ) (x : σ → ℕ) (prime : V → ℕ)
    (henv : ∀ i, (env i).value (fun j => (a j : ℚ)) = (x i : ℚ))
    (hv : ValidTransferHistory (wordTransferSystem σ) n (template.state x) t) :
    (∀ g ∈ D.checks template t ht env, g.Holds a prime) ↔ D.ValidAt template x prime t := by
  induction template generalizing env x with
  | leaf word => cases D; simp only [checks, List.not_mem_nil, false_implies, implies_true, ValidAt]
  | @node n d l r ihL ihR =>
    cases D with
    | node coordinates L R =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      have hu := wordTransferUpdatedFormulas_nat d l r x _ _ _ ht.1 P hp env a henv
      have hpv := wordTransfer_pivot_formula_value d l r x _ _ _ ht.1 P hp env a henv
      have hpi := HistoryFormula.integerValue_of_value _ a (P : ℤ) hpv
      simp only [checks, List.forall_mem_append, List.forall_mem_map, ValidAt,
        hp.historyPivot_eq, HistoryPrimeCheck.Holds, hpi, Int.natAbs_natCast]
      exact and_congr Iff.rfl
        (and_congr (ihL L t.2.1 ht.2.1 _ _ hu hvL) (ihR R t.2.2 ht.2.2 _ _ hu hvR))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ExpandedPrimeReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual Y-atom coprimalities are a finite list of original-prime checks -/

namespace Ostmann

open scoped Classical

theorem expandedYPrimeCoordinates_coprime {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable V depth))
    (hc : ExpandedActualCoordinates role depth (n + 1) current)
    (x : ExpandedScheduledVariable V depth → ℕ) (prime : V → ℕ)
    (hx : ∀ v, x (.inl v) = prime v) (P : ℕ) :
    (∀ v ∈ expandedYPrimeCoordinates role depth n current, (prime v).Coprime P) ↔
      ∀ i : CopyScheduleY role n,
        (expandedAtomValues role (n + 1) current x ⟨.inr i.val, i.property⟩).Coprime P := by
  have he (i : CopyScheduleY role n) :
      ((expandedYPrimeWord role depth n current i).map prime).prod =
        expandedAtomValues role (n + 1) current x ⟨.inr i.val, i.property⟩ := by
    rw [← expandedYPrimeWord_product role depth n current hc i x]
    congr 1
    exact List.map_congr_left (fun v _ => (hx v).symm)
  constructor
  · intro h i
    rw [← he i, Nat.coprime_list_prod_left_iff]
    intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact h v (List.mem_flatMap.mpr ⟨i, by simp, hv⟩)
  · intro h v hv
    obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
    have hi := h i
    rw [← he i, Nat.coprime_list_prod_left_iff] at hi
    exact hi _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem expandedSchedulePrimes_valid_iff {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (depth n : ℕ) (hn : n ≤ depth) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable V depth))
    (hc : ∀ i v, v ∈ current i → ExpandedCoordinateAfter n v)
    (ha : ExpandedActualCoordinates role depth n current)
    (x : ExpandedScheduledVariable V depth → ℕ) (prime : V → ℕ)
    (hx : ∀ v, x (.inl v) = prime v) (t : FrequencyTree ℤ n) :
    (expandedSchedulePrimes role depth n path current).ValidAt
        (expandedScheduledTemplate role (expandedPivotAddress V depth) childBound pivotBound n path current)
        x prime t ↔
      scheduleAtomCoprimalitiesValid role childBound pivotBound n
        (expandedAtomValues role n current x) t := by
  induction n generalizing path x with
  | zero => rfl
  | succ n ih =>
    let P := historyPivot (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, expandedAtomValues role (n + 1) current x⟩
      t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    have hn' : n ≤ depth := by omega
    have hx' (v : V) :
        Function.update x (expandedPivotAddress V depth n path) P (.inl v) = prime v := by
      simpa only [expandedPivotAddress, Function.update_of_ne (Sum.inl_ne_inr)] using hx v
    have hL := ih hn' (true :: path)
      (reverseCopyLabelMap role n true [expandedPivotAddress V depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' true path current hc)
      (reverseExpandedActualCoordinates role depth n true _ current ha)
      (Function.update x (expandedPivotAddress V depth n path) P) hx' t.2.1
    have hR := ih hn' (false :: path)
      (reverseCopyLabelMap role n false [expandedPivotAddress V depth n path] current)
      (reverseExpandedCoordinates_after role depth n hn' false path current hc)
      (reverseExpandedActualCoordinates role depth n false _ current ha)
      (Function.update x (expandedPivotAddress V depth n path) P) hx' t.2.2
    rw [expanded_schedule_child_state role depth n hn' true path current hc x P] at hL
    rw [expanded_schedule_child_state role depth n hn' false path current hc x P] at hR
    have hp := expanded_schedule_pivot_eq role (expandedPivotAddress V depth)
      childBound pivotBound n path current x t.1 (frequencyRoot n t.2.1) (frequencyRoot n t.2.2)
    dsimp only [expandedScheduledTemplate] at hp
    simp only [expandedSchedulePrimes, expandedScheduledTemplate, WordPrimeDecoration.ValidAt,
      hp, scheduleAtomCoprimalitiesValid]
    apply and_congr (expandedYPrimeCoordinates_coprime role depth n current ha x prime hx P)
    apply and_congr
    · convert hL using 2
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _
    · convert hR using 2
      all_goals try with_reducible_and_instances rfl
      congr 2
      exact Subsingleton.elim _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedUnitCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original all-atom frequency-units in the ranged Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

/-- Each actual atom is a unit modulo the frequency of every state in which
it occurs. These conditions remain inside the exact polynomial coefficient. -/
theorem groupedUnitRangedFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedUnitRangedFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).unitRangedCoefficient
        (expandedRootRanges role n words (totalAtomUnitRanges role))
        (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
        t ht (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  let p := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
  have he := p.unitRangedCoefficient_nat_all
    (expandedRootRanges role n words (totalAtomUnitRanges role)) (expandedRootRanges role n words ranges)
    (expandedRootTemplate role n words childBound pivotBound) t ht (expandedPrimeNatValues n x)
  rw [expandedPrimeNatValues_cast] at he
  have hunit := expandedScheduleUnits_valid_iff role childBound pivotBound (totalAtomUnitRanges role)
    n n le_rfl [] (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role n words)
    (expandedPrimeNatValues n x) t
  have hx : expandedAtomValues role n (fun i => (words i).map Sum.inl) (expandedPrimeNatValues n x) =
      fun i => ((words i).map x).prod := by
    funext i
    unfold expandedAtomValues
    rw [List.map_map]
    rfl
  rw [hx] at hunit
  have hbase := groupedRangedFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht x
  rw [he, ← hbase]
  unfold groupedUnitRangedFourierWeight
  congr 1
  simp only [expandedRootRanges, expandedRootTemplate, hunit]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The coefficient retaining the large-prime coprimality support -/

namespace Ostmann.WordFourierParameters

open scoped Classical

/-- This identity also covers invalid histories: both coefficients vanish. -/
theorem primeUnitRangedCoefficient_nat {V : Type*} {n : ℕ} (p : WordFourierParameters n)
    (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    p.primeUnitRangedCoefficient C U D template t ht x =
      (if C.ValidAt template (expandedPrimeNatValues n x) x t then 1 else 0) *
        p.unitRangedCoefficient U D template t ht (expandedPrimeValues n (fun i => (x i : ℤ))) := by
  by_cases hv : ValidTransferHistory (wordTransferSystem (ExpandedScheduledVariable V n)) n
      (template.state (expandedPrimeNatValues n x)) t
  · have he := C.checks_iff template t ht .prime
      (expandedPrimeValues n (fun i => (x i : ℤ))) (expandedPrimeNatValues n x) x
      (by intro i; simp only [HistoryFormula.value_prime]; cases i <;>
        simp only [expandedPrimeValues, expandedPrimeNatValues, Int.cast_natCast, Int.cast_one, Nat.cast_one]) hv
    unfold primeUnitRangedCoefficient
    simp only [he]
    split_ifs <;> simp only [one_mul, zero_mul]
  · have hz : p.unitRangedCoefficient U D template t ht
        (expandedPrimeValues n (fun i => (x i : ℤ))) = 0 := by
      rw [← expandedPrimeNatValues_cast]
      simp only [unitRangedCoefficient, rangedCoefficient,
        p.coefficient_eq_zero_of_not_valid template t ht _ hv, mul_zero]
    simp only [primeUnitRangedCoefficient, hz, ite_self, mul_zero]

end Ostmann.WordFourierParameters

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedCoprimeCoefficient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reconstructed Y-coprimalities in the original grouped Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem groupedCoprimeFourierWeight_coefficient {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    groupedCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
        (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
        (expandedRootRanges role n words (totalAtomUnitRanges role))
        (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
        t ht x := by
  let p := WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi
  rw [p.primeUnitRangedCoefficient_nat]
  have he := expandedSchedulePrimes_valid_iff role childBound pivotBound n n le_rfl []
    (fun i => (words i).map Sum.inl) (expandedRootCoordinates_after role n words)
    (expandedRoot_actual_coordinates role n words) (expandedPrimeNatValues n x) x (fun _ => rfl) t
  have hx : expandedAtomValues role n (fun i => (words i).map Sum.inl) (expandedPrimeNatValues n x) =
      fun i => ((words i).map x).prod := by
    funext i
    unfold expandedAtomValues
    rw [List.map_map]
    rfl
  rw [hx] at he
  unfold groupedCoprimeFourierWeight
  rw [groupedUnitRangedFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht x]
  congr 1
  simp only [expandedRootTemplate, he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleInheritedCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A reconstructed pivot inherits coprimality with both H copies -/

namespace Ostmann

open scoped BigOperators Classical

theorem schedule_pivot_coprime_all {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (x : CopyScheduleAtoms role (n + 1) → ℕ)
    (P : ℕ) (s v w : ℤ)
    (hpair : Pairwise (fun i j => (x i).Coprime (x j)))
    (hleft : (∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩).Coprime v.natAbs)
    (hright : (∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩).Coprime w.natAbs)
    (hrel : v * (∏ i : CopyScheduleH role n, (x ⟨.inl (false, i.val), i.property⟩ : ℤ)) -
      w * (∏ i : CopyScheduleH role n, (x ⟨.inl (true, i.val), i.property⟩ : ℤ)) = s * P)
    (hY : ∀ i : CopyScheduleY role n, P.Coprime (x ⟨.inr i.val, i.property⟩)) :
    ∀ i, P.Coprime (x i) := by
  let L := ∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩
  let R := ∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩
  have hLR : L.Coprime R := Nat.coprime_fintype_prod_left_iff.mpr (fun i =>
    Nat.coprime_fintype_prod_right_iff.mpr (fun j => hpair (by
      intro h
      have he := congrArg Subtype.val h
      cases congrArg Prod.fst (Sum.inl.inj he))))
  have hv : IsCoprime v (L : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.gcd v.natAbs L = 1
    exact hleft.symm
  have hw : IsCoprime w (R : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change Nat.gcd w.natAbs R = 1
    exact hright.symm
  have hr : v * (R : ℤ) - w * (L : ℤ) = s * 1 * (P : ℤ) := by
    simpa only [L, R, Nat.cast_prod, mul_one] using hrel
  have hcop := (reversal_inherited_coprime v w (L : ℤ) (R : ℤ) s 1 P
    hLR.isCoprime hv hw hr).1
  have hP : P.Coprime (L * R) := Nat.isCoprime_iff_coprime.mp (by
    simpa only [Nat.cast_mul] using hcop)
  have hPL := Nat.coprime_fintype_prod_right_iff.mp (Nat.coprime_mul_iff_right.mp hP).1
  have hPR := Nat.coprime_fintype_prod_right_iff.mp (Nat.coprime_mul_iff_right.mp hP).2
  intro i
  rcases i with ⟨i, hi⟩
  cases i with
  | inl p =>
    rcases p with ⟨b, i⟩
    cases b
    · exact hPR ⟨i, hi⟩
    · exact hPL ⟨i, hi⟩
  | inr i => exact hY ⟨i, hi⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ReverseCopyCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pairwise coprimality survives a reverse copy step -/

namespace Ostmann

open scoped Classical

theorem CopyScheduleRole.erasedAt_eq_true_iff (r : CopyScheduleRole) (n : ℕ) :
    r.erasedAt n = true ↔ r = .pivot n := by
  cases r <;> simp [erasedAt, eq_comm]

theorem erased_schedule_atoms_unique {I : Type*} (role : I → CopyScheduleRole) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b)
    (i j : CopyScheduleAtoms role n)
    (hi : (copyScheduleRole role n i.val).erasedAt n = true)
    (hj : (copyScheduleRole role n j.val).erasedAt n = true) : i = j := by
  obtain ⟨_, a, ha, hea⟩ := surviving_pivot_is_positive role n n i.val i.property
    ((CopyScheduleRole.erasedAt_eq_true_iff _ _).mp hi)
  obtain ⟨_, b, hb, heb⟩ := surviving_pivot_is_positive role n n j.val j.property
    ((CopyScheduleRole.erasedAt_eq_true_iff _ _).mp hj)
  apply Subtype.ext
  rw [hea, heb, hu a b ha hb]

theorem reverseCopyLabelMap_pairwise_coprime {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (P : ℕ) (x : CopyScheduleAtoms role (n + 1) → ℕ)
    (hu : ∀ a c, role a = .pivot n → role c = .pivot n → a = c)
    (hpair : Pairwise (fun i j => (x i).Coprime (x j)))
    (hP : ∀ i, P.Coprime (x i)) :
    Pairwise (fun i j => (reverseCopyLabelMap role n b P x i).Coprime
      (reverseCopyLabelMap role n b P x j)) := by
  intro i j hij
  unfold reverseCopyLabelMap
  split_ifs with hic hjc hje hie hjc hje hjc hje
  · apply hpair
    intro he
    apply hij
    apply Subtype.ext
    exact (Prod.mk.inj (Sum.inl.inj (congrArg Subtype.val he))).2
  · exact (hP _).symm
  · apply hpair
    intro he
    have hv := congrArg Subtype.val he
    cases hv
  · exact hP _
  · exact False.elim (hij (erased_schedule_atoms_unique role n hu i j hie hje))
  · exact hP _
  · apply hpair
    intro he
    have hv := congrArg Subtype.val he
    cases hv
  · exact (hP _).symm
  · apply hpair
    intro he
    apply hij
    exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val he))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_SchedulePairwiseReplay
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The reduced support implies every original pairwise-coprimality gate -/

namespace Ostmann

open scoped BigOperators Classical

theorem scheduleAtomUnitsValid_root {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    ∀ i, (x i).Coprime (frequencyRoot n t).natAbs := by
  cases n with
  | zero => exact (totalAtomUnitRanges_iff role 0 x t).mp hu
  | succ n => exact (totalAtomUnitRanges_iff role (n + 1) x t.1).mp hu.1

/-- All H-coprimalities are forced by the signed reconstruction and inherited
frequency-units. Only the Y checks and top pairwise support need be retained. -/
theorem schedule_pairwise_of_reduced_support {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t)
    (hunits : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t)
    (hY : scheduleAtomCoprimalitiesValid role childBound pivotBound n x t)
    (hpair : Pairwise (fun i j => (x i).Coprime (x j))) :
    scheduleAtomPairwiseValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact hpair
  | succ n ih =>
    obtain ⟨P, hp, hvL, hvR⟩ := hv
    simp only [scheduleAtomUnitsValid, hp.historyPivot_eq] at hunits
    simp only [scheduleAtomCoprimalitiesValid, hp.historyPivot_eq] at hY
    simp only [scheduleAtomPairwiseValid, hp.historyPivot_eq]
    have hL := scheduleAtomUnitsValid_root role childBound pivotBound n
      (reverseCopyLabelMap role n true P x) t.2.1 hunits.2.1
    have hR := scheduleAtomUnitsValid_root role childBound pivotBound n
      (reverseCopyLabelMap role n false P x) t.2.2 hunits.2.2
    have hleft : (∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩).Coprime
        (frequencyRoot n t.2.1).natAbs := by
      apply Nat.coprime_fintype_prod_left_iff.mpr
      intro i
      have hh := hL ⟨i.val, i.property.1⟩
      rw [reverseCopyLabelMap_copied] at hh
      exact hh
    have hright : (∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩).Coprime
        (frequencyRoot n t.2.2).natAbs := by
      apply Nat.coprime_fintype_prod_left_iff.mpr
      intro i
      have hh := hR ⟨i.val, i.property.1⟩
      rw [reverseCopyLabelMap_copied] at hh
      exact hh
    have hP := schedule_pivot_coprime_all role n x P t.1
      (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hpair hleft hright
      (by simpa only [scheduleAtomSystem, scheduleAtomLeft, scheduleAtomRight, Nat.cast_prod] using hp.relation)
      (fun i => (hY.1 i).symm)
    have hu' : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b :=
      fun j hj => hu j (by omega)
    refine ⟨hpair, ?_, ?_⟩
    · exact ih _ t.2.1 hu' hvL hunits.2.1 hY.2.1
        (reverseCopyLabelMap_pairwise_coprime role n true P x (hu n (by omega)) hpair hP)
    · exact ih _ t.2.2 hu' hvR hunits.2.2 hY.2.2
        (reverseCopyLabelMap_pairwise_coprime role n false P x (hu n (by omega)) hpair hP)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduleFullCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering the complete large-coprimality support from the reduced tests -/

namespace Ostmann

open scoped BigOperators Classical

theorem schedule_full_coprime_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (h : scheduleAtomFullCoprimeValid role childBound pivotBound n x t) :
    Pairwise (fun i j => (x i).Coprime (x j)) ∧
      scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  induction n with
  | zero => exact ⟨h, trivial⟩
  | succ n ih =>
    exact ⟨h.1, (fun i => (h.2.1 _).symm), (ih _ _ h.2.2.1).2,
      (ih _ _ h.2.2.2).2⟩

/-- There is no loss of original support: all the omitted H tests follow
from the reconstruction equation and the retained frequency-unit tests. -/
theorem schedule_full_coprime_iff_reduced {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
    (hv : ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n ⟨n, x⟩ t)
    (hunits : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n x t) :
    scheduleAtomFullCoprimeValid role childBound pivotBound n x t ↔
      Pairwise (fun i j => (x i).Coprime (x j)) ∧
        scheduleAtomCoprimalitiesValid role childBound pivotBound n x t := by
  constructor
  · exact schedule_full_coprime_reduced role childBound pivotBound n x t
  · rintro ⟨hpair, hY⟩
    have hall := schedule_pairwise_of_reduced_support role childBound pivotBound n x t
      hu hv hunits hY hpair
    clear hpair
    induction n with
    | zero => exact hall
    | succ n ih =>
      obtain ⟨P, hp, hvL, hvR⟩ := hv
      simp only [scheduleAtomUnitsValid, hp.historyPivot_eq] at hunits
      simp only [scheduleAtomCoprimalitiesValid, hp.historyPivot_eq] at hY
      simp only [scheduleAtomPairwiseValid, hp.historyPivot_eq] at hall
      simp only [scheduleAtomFullCoprimeValid, hp.historyPivot_eq]
      have hL := scheduleAtomUnitsValid_root role childBound pivotBound n
        (reverseCopyLabelMap role n true P x) t.2.1 hunits.2.1
      have hR := scheduleAtomUnitsValid_root role childBound pivotBound n
        (reverseCopyLabelMap role n false P x) t.2.2 hunits.2.2
      have hleft : (∏ i : CopyScheduleH role n, x ⟨.inl (true, i.val), i.property⟩).Coprime
          (frequencyRoot n t.2.1).natAbs := by
        apply Nat.coprime_fintype_prod_left_iff.mpr
        intro i
        simpa only [reverseCopyLabelMap_copied] using hL ⟨i.val, i.property.1⟩
      have hright : (∏ i : CopyScheduleH role n, x ⟨.inl (false, i.val), i.property⟩).Coprime
          (frequencyRoot n t.2.2).natAbs := by
        apply Nat.coprime_fintype_prod_left_iff.mpr
        intro i
        simpa only [reverseCopyLabelMap_copied] using hR ⟨i.val, i.property.1⟩
      have hP := schedule_pivot_coprime_all role n x P t.1
        (frequencyRoot n t.2.1) (frequencyRoot n t.2.2) hall.1 hleft hright
        (by simpa only [scheduleAtomSystem, scheduleAtomLeft, scheduleAtomRight, Nat.cast_prod]
            using hp.relation)
        (fun i => (hY.1 i).symm)
      have hu' : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b :=
        fun j hj => hu j (by omega)
      exact ⟨hall.1, hP, ih _ _ hu' hvL hunits.2.1 hY.2.1 hall.2.1,
        ih _ _ hu' hvR hunits.2.2 hY.2.2 hall.2.2⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedFullCoprime
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The original complete coprimality support in the grouped Fourier weight -/

namespace Ostmann

open scoped Classical SchwartzMap FourierTransform ComplexConjugate

theorem groupedUnitRangedFourierWeight_support {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ)
    (hn : groupedUnitRangedFourierWeight role n words childBound pivotBound ranges
      ψ X lo hi t x ≠ 0) :
    ValidTransferHistory (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, fun i => ((words i).map x).prod⟩ t ∧
    scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (fun i => ((words i).map x).prod) t := by
  unfold groupedUnitRangedFourierWeight at hn
  obtain ⟨hu, hr⟩ := mul_ne_zero_iff.mp hn
  have hu' : scheduleAtomUnitsValid role childBound pivotBound (totalAtomUnitRanges role) n
      (fun i => ((words i).map x).prod) t := by
    by_contra h
    simp only [h, ite_false, if_false, ne_eq, not_true_eq_false] at hu
  unfold groupedRangedFourierWeight at hr
  have hb := (mul_ne_zero_iff.mp hr).2
  exact ⟨recursiveTransferWeight_nonzero_valid _ _ _ _ _ _ hb, hu'⟩

theorem groupedFullCoprimeFourierWeight_reduced {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (x : V → ℕ)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      if Pairwise (fun i j => ((words i).map x).prod.Coprime ((words j).map x).prod) then
        groupedCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x
      else 0 := by
  by_cases hn : groupedUnitRangedFourierWeight role n words childBound pivotBound ranges
      ψ X lo hi t x = 0
  · simp only [groupedFullCoprimeFourierWeight, groupedCoprimeFourierWeight, hn, mul_zero, ite_self]
  · obtain ⟨hv, hunit⟩ := groupedUnitRangedFourierWeight_support role n words childBound
      pivotBound ranges ψ X lo hi t x hn
    have he := schedule_full_coprime_iff_reduced role childBound pivotBound n
      (fun i => ((words i).map x).prod) t hu hv hunit
    simp only [groupedFullCoprimeFourierWeight, groupedCoprimeFourierWeight, he]
    split_ifs <;> simp_all

/-- The original large-coprimality gates are represented exactly, even on
invalid histories, by the explicit top prime tests and reconstructed Y tests. -/
theorem groupedFullCoprimeFourierWeight_coefficient_oai {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t x =
      if ∀ c ∈ atomPairChecks words, c.Holds x then
        (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi).primeUnitRangedCoefficient
          (expandedSchedulePrimes role n n [] (fun i => (words i).map Sum.inl))
          (expandedRootRanges role n words (totalAtomUnitRanges role))
          (expandedRootRanges role n words ranges) (expandedRootTemplate role n words childBound pivotBound)
          t ht x
      else 0 := by
  rw [groupedFullCoprimeFourierWeight_reduced role n words childBound pivotBound ranges
    ψ X lo hi t x hu, groupedCoprimeFourierWeight_coefficient role n words childBound
    pivotBound ranges ψ hreal X lo hi hlo hhi t ht x]
  simp only [atomPairChecks_iff]

end Ostmann

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient_oai.{u_1, u_2} := @OAI.Ostmann.groupedFullCoprimeFourierWeight_coefficient_oai.{u_1, u_2}
