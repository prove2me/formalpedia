-- Prove2me | solution 1 for OAI.Ostmann.constituent_final_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:03:06.54152+00:00
-- url     : https://prove2.me/submissions/9bdaec98-07e0-4218-8a66-a01e42ba8614

import Mathlib
import Definitions.Def_OAIQ095D007
import Theorems.Thm_OAI_Ostmann_fixed_pivot_full_original_pair_bound
import Theorems.Thm_OAI_Ostmann_groupedFullCoprimeFourierWeight_coefficient

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

end ClearedHistoryValue

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph update and the regular-row invariant in one transfer -/

namespace Ostmann

theorem transferredGraph_diagonal {H Y : Type*}
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ) (hb : ∀ i, b i i = 0) :
    ∀ i, transferredGraph b i i = 0 := by
  intro i
  cases i with
  | inl q => simp [transferredGraph, hb]
  | inr y => rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_TransferLocalPhases
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local additive and character substitutions in one transfer -/

namespace Ostmann

open scoped ComplexConjugate

theorem conjugate_character_power {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (b : ℤ) : conj (χ x ^ b) = χ x ^ (-b) := by
  change star (χ x ^ b) = _
  rw [star_zpow₀, MulChar.star_apply', MulChar.inv_apply_eq_inv', inv_zpow, zpow_neg]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PivotRowPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded pivot row after grouping by v/H -/

namespace Ostmann

open scoped BigOperators

theorem character_zpow_norm_le_one {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (ε : ℤ) : ‖χ x ^ ε‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simp only [norm_zpow, χ.unit_norm_eq_one, one_zpow, le_refl]
  · rw [χ.map_nonunit hx]
    by_cases he : ε = 0
    · simp [he]
    · simp [zero_zpow, he]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PermutedAdditiveCancellation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common-center additive phases cancel under the actual matching -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem tupleCofactor_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (i : I) :
    tupleCofactor (fun i => p (e i)) i = tupleCofactor p (e i) := by
  apply mul_left_cancel₀ (hp (e i))
  calc
    _ = ∏ j, p (e j) := tupleCofactor_mul _ i
    _ = ∏ j, p j := e.prod_comp p
    _ = _ := (tupleCofactor_mul p (e i)).symm

theorem primeTupleAdditivePhase_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → ℕ) (hp : ∀ j, p j ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ) :
    primeTupleAdditivePhase (fun i => p (e i)) (fun i => hp (e i)) t v =
      primeTupleAdditivePhase p hp t v := by
  let : ∀ j, NeZero (p j) := fun j => ⟨hp j⟩
  unfold primeTupleAdditivePhase
  simp_rw [tupleCofactor_equiv e p hp]
  exact e.prod_comp (fun j => (ZMod.stdAddChar
    (t (p j) * ((tupleCofactor p j : ZMod (p j))⁻¹ * (v : ZMod (p j)))) : ℂ))

theorem primeTupleAdditivePhase_norm {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (t : ∀ p : ℕ, ZMod p) (v : ℤ) :
    ‖primeTupleAdditivePhase p hp t v‖ = 1 := by
  unfold primeTupleAdditivePhase
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  simp only [ZMod.stdAddChar_apply, Circle.norm_coe]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GraphCopySchedule
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.copyScheduleVertexFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph on the literal copied and retained slot labels

The ambient label type includes both alternatives at a transfer. The actual
partition restricts the copied alternative to H and the retained alternative to
Y. Thus copying and retaining never identify two surviving slots. -/

namespace Ostmann

universe u

theorem copyScheduleGraph_diagonal {I : Type*} (g : I → I → ℤ) (pivot : ℕ → I)
    (hg : ∀ i, g i i = 0) (n : ℕ) : ∀ i, copyScheduleGraph g pivot n i i = 0 := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    apply transferredGraph_diagonal
    intro i
    exact ih _

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

theorem value_listProduct (fs : List (HistoryFormula σ)) (x : σ → ℚ) :
    (listProduct fs).value x = (fs.map (fun F => F.value x)).prod := by
  induction fs with
  | nil => simp [listProduct]
  | cons f fs ih => simp only [listProduct, value_product, List.map_cons, List.prod_cons, ih]

end Ostmann.HistoryFormula

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

end BranchingWordHistory
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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedGraphQuotient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The graph quotient under an actual matching of the prime variables -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem finiteEdgeWeight_equiv {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (E : J → J → ℕ → ℕ → ℂ) (ν : J → ℕ → ℂ) (p : J → ℕ) :
    finiteEdgeWeight (fun i j => E (e i) (e j)) (fun i => ν (e i)) (fun i => p (e i)) =
      finiteEdgeWeight E ν p := by
  unfold finiteEdgeWeight
  calc
    _ = ∏ i, ν (e i) (p (e i)) * ∏ j, E (e i) j (p (e i)) (p j) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [e.prod_comp (fun j => E (e i) j (p (e i)) (p j))]
    _ = _ := e.prod_comp (fun i => ν i (p i) * ∏ j, E i j (p i) (p j))

theorem dirichlet_graph_quotient {I : Type*} [Fintype I]
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b c : I → I → ℤ) (ν ω : I → ℕ → ℂ) (p : I → ℕ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b i i = 0) (hcdiag : ∀ i, c i i = 0) :
    finiteEdgeWeight (dirichletGraphEdge χ b) ν p *
        conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω p) =
      finiteEdgeWeight (dirichletGraphEdge χ (graphDifference b c))
        (fun i x => ν i x * conj (ω i x)) p := by
  unfold finiteEdgeWeight
  rw [map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [map_mul, map_prod]
  rw [show (ν i (p i) * ∏ j, dirichletGraphEdge χ b i j (p i) (p j)) *
      (conj (ω i (p i)) * ∏ j, conj (dirichletGraphEdge χ c i j (p i) (p j))) =
      (ν i (p i) * conj (ω i (p i))) *
        ((∏ j, dirichletGraphEdge χ b i j (p i) (p j)) *
          ∏ j, conj (dirichletGraphEdge χ c i j (p i) (p j))) by ring]
  rw [← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [dirichletGraphEdge, graphDifference, hb, hcdiag, sub_self,
      zpow_zero, map_one, mul_one]
  · have hu : IsUnit (p j : ZMod (p i)) :=
      (ZMod.isUnit_iff_coprime _ _).mpr (hc hij).symm
    have hn : χ i (p i) (p j : ZMod (p i)) ≠ 0 :=
      MulChar.apply_ne_zero_iff.mpr hu
    simp only [dirichletGraphEdge, graphDifference, conjugate_character_power]
    rw [← zpow_add₀ hn, sub_eq_add_neg]

theorem graphQuotientUnary_norm {I : Type*} (ν ω : I → ℕ → ℂ)
    (hν : ∀ i x, ‖ν i x‖ ≤ 1) (hω : ∀ i x, ‖ω i x‖ ≤ 1) (i : I) (x : ℕ) :
    ‖ν i x * conj (ω i x)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_conj]
  exact (mul_le_mul (hν i x) (hω i x) (norm_nonneg _) (by norm_num)).trans
    (by norm_num)

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

theorem atomPairChecks_bounded {I V : Type*} [Fintype I]
    (words : I → List V) (R : ℝ) :
    ∀ c ∈ atomPairChecks words, c.Bounded R := by
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
  by_cases hij : i = j
  · simp only [hij, ite_true, if_true, List.not_mem_nil] at hc
  · simp only [hij, ite_false, if_false] at hc
    obtain ⟨v, _, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hc
    trivial

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

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FullAtomTransferWeight
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete grouped weight as a single supported recursive weight -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

/-- Evaluation at arbitrary words is just evaluation at their atom products. -/
theorem groupedFullCoprimeFourierWeight_atom {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (q : V → ℕ) :
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t q =
      fullAtomTransferWeight role childBound pivotBound ranges
        (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
          normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
        n (fun i => ((words i).map q).prod) t := by
  unfold groupedFullCoprimeFourierWeight groupedUnitRangedFourierWeight
    groupedRangedFourierWeight groupedScheduleFourierWeight fullAtomTransferWeight fullAtomWeightGuard
  split_ifs <;> simp_all

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_CopyScheduleUnary
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual unary factors on the copied schedule -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem copyScheduleUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (g : I → I → ℤ) (pivot : ℕ → I) (initial : I → ℤ → ℕ → ℂ)
    (hinit : ∀ i v p, ‖initial i v p‖ ≤ 1)
    (n : ℕ) (t : FrequencyTree ℤ n) (i : CopyScheduleVertex I n) (p : ℕ) :
    ‖copyScheduleUnary χ g pivot initial n t i p‖ ≤ 1 := by
  induction n with
  | zero => exact hinit i t p
  | succ n ih =>
    rcases i with ⟨c, i⟩ | i
    · cases c
      · rw [copyScheduleUnary, norm_mul, Complex.norm_conj]
        exact (mul_le_mul (ih t.2.2 i) (character_zpow_norm_le_one _ _ _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num)
      · rw [copyScheduleUnary, norm_mul]
        exact (mul_le_mul (ih t.2.1 i) (character_zpow_norm_le_one _ _ _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num)
    · rw [copyScheduleUnary, norm_mul, Complex.norm_conj]
      exact (mul_le_mul (ih t.2.1 i) (ih t.2.2 i) (norm_nonneg _) (by norm_num)).trans (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledPhaseNorm
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform modulus bounds for the literal scheduled prime phase -/

namespace Ostmann
open scoped Classical

theorem initialRegularUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (i : I) (v : ℤ) (p : ℕ) :
    ‖initialRegularUnary χ κ i v p‖ ≤ 1 := by
  unfold initialRegularUnary regularUnary
  rw [norm_mul]
  exact (mul_le_mul (hκ i p) (character_zpow_norm_le_one _ _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedDirectedPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Full phase quotients have the transported graph difference -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem directedPrimePhase_split {I : Type*} [Fintype I]
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (t : ∀ p : ℕ, ZMod p)
    (ν : I → ℕ → ℂ) (b : I → I → ℤ) (v : ℤ) :
    let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
    directedPrimePhase p (fun i => χ i (p i)) (fun i => t (p i))
      (fun i => ν i (p i)) b v =
      primeTupleAdditivePhase p hp t v * finiteEdgeWeight (dirichletGraphEdge χ b) ν p := by
  dsimp only
  simp only [directedPrimePhase, primeTupleAdditivePhase, finiteEdgeWeight,
    dirichletGraphEdge, mul_assoc, Finset.prod_mul_distrib]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedInvariantCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Matching preserves the character carried by each moved slot -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem finiteEdgeWeight_invariant_transport {V : Type*} [Fintype V]
    (e : Equiv.Perm V) (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i, χ (e i) = χ i) (b : V → V → ℤ) (ν : V → ℕ → ℂ) (p : V → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge χ b) ν (p ∘ e) =
      finiteEdgeWeight (dirichletGraphEdge χ (transportGraph e b))
        (fun i => ν (e.symm i)) p := by
  simpa only [finiteEdgeWeight, Function.comp_def, transportGraph, dirichletGraphEdge,
    Equiv.symm_apply_apply, hχ] using
      finiteEdgeWeight_equiv e (dirichletGraphEdge χ (transportGraph e b))
        (fun i => ν (e.symm i)) p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_DirectedPhaseQuotient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact cancellation at a shared root frequency on all prime coordinates -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem directedPrimePhase_invariant_pair {I : Type*} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, p i ≠ 0) (e : Equiv.Perm I)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ i, χ (e i) = χ i)
    (center : ∀ p : ℕ, ZMod p) (ν ω : I → ℕ → ℂ)
    (b c : I → I → ℤ) (v : ℤ)
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (hb : ∀ i, b i i = 0) (hcdiag : ∀ i, c i i = 0) :
    let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
    let : ∀ i, NeZero (p (e i)) := fun i => ⟨hp (e i)⟩
    directedPrimePhase p (fun i => χ i (p i)) (fun i => center (p i))
        (fun i => ν i (p i)) b v *
      conj (directedPrimePhase (fun i => p (e i)) (fun i => χ i (p (e i)))
        (fun i => center (p (e i))) (fun i => ω i (p (e i))) c v) =
      finiteEdgeWeight (dirichletGraphEdge χ (graphDifference b (transportGraph e c)))
        (fun i q => ν i q * conj (ω (e.symm i) q)) p := by
  let : ∀ i, NeZero (p i) := fun i => ⟨hp i⟩
  let : ∀ i, NeZero (p (e i)) := fun i => ⟨hp (e i)⟩
  dsimp only
  rw [directedPrimePhase_split χ p hp center ν b v,
    directedPrimePhase_split χ (fun i => p (e i)) (fun i => hp (e i)) center ω c v]
  rw [primeTupleAdditivePhase_equiv e p hp]
  have hunit : primeTupleAdditivePhase p hp center v *
      conj (primeTupleAdditivePhase p hp center v) = 1 := by
    rw [Complex.mul_conj', primeTupleAdditivePhase_norm]
    norm_num
  rw [map_mul]
  calc
    _ = finiteEdgeWeight (dirichletGraphEdge χ b) ν p *
        conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω (fun i => p (e i))) := by
      calc
        _ = (primeTupleAdditivePhase p hp center v * conj (primeTupleAdditivePhase p hp center v)) *
            (finiteEdgeWeight (dirichletGraphEdge χ b) ν p *
              conj (finiteEdgeWeight (dirichletGraphEdge χ c) ω (fun i => p (e i)))) := by ring
        _ = _ := by rw [hunit, one_mul]
    _ = _ := by
      have he := finiteEdgeWeight_invariant_transport e χ hχ c ω p
      dsimp only [Function.comp_def] at he
      rw [he]
      exact dirichlet_graph_quotient χ b (transportGraph e c) ν (fun i => ω (e.symm i)) p hc hb
        (fun i => hcdiag (e.symm i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledSampleQuotient
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal full scheduled phase quotient at a common root -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem scheduledSamplePhase_invariant_pair {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (n : ℕ) (t t' : FrequencyTree ℤ n)
    (hroot : frequencyRoot n t = frequencyRoot n t')
    (e : Equiv.Perm (CopyScheduleAtoms role n))
    (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (q : CopyScheduleAtoms role n → P)
    (hq : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)))
    (center : ∀ p : ℕ, ZMod p) :
    scheduledSamplePhase role χ κ pivot n t P hP q center *
      conj (scheduledSamplePhase role χ κ pivot n t' P hP (fun i => q (e i)) center) =
      finiteEdgeWeight
        (dirichletGraphEdge (fun i => χ (copyScheduleOrigin n i.val))
          (graphDifference (scheduledSurvivorGraph role pivot n)
            (transportGraph e (scheduledSurvivorGraph role pivot n))))
        (fun i p => scheduledSurvivorUnary role χ κ pivot n t i p *
          conj (scheduledSurvivorUnary role χ κ pivot n t' (e.symm i) p))
        (fun i => (q i : ℕ)) := by
  unfold scheduledSamplePhase scheduledPrimePhase
  dsimp only
  rw [← hroot]
  exact directedPrimePhase_invariant_pair (fun i => (q i : ℕ))
    (fun i => (hP _ (q i).property).ne_zero) e
    (fun i => χ (copyScheduleOrigin n i.val)) hχ center
    (scheduledSurvivorUnary role χ κ pivot n t)
    (scheduledSurvivorUnary role χ κ pivot n t')
    (scheduledSurvivorGraph role pivot n) (scheduledSurvivorGraph role pivot n)
    (frequencyRoot n t) hq
    (fun i => copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n i.val)
    (fun i => copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n i.val)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact final fixed-history pair, with all original support guards -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituentPrimeTerm_pair {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t t' : FrequencyTree ℤ n)
    (hroot : frequencyRoot n t = frequencyRoot n t')
    (e : Equiv.Perm (SurvivingConstituent role size n))
    (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
    (q : SurvivingConstituent role size n → P) (center : ∀ p : ℕ, ZMod p) :
    constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))) =
      if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
        finiteEdgeWeight
          (dirichletGraphEdge (fun i => χ (copyScheduleOrigin n i.val))
            (graphDifference
              (scheduledSurvivorGraph (fun i : Σ a, Fin (size a) => role i.1) pivot n)
              (transportGraph e (scheduledSurvivorGraph
                (fun i : Σ a, Fin (size a) => role i.1) pivot n))))
          (fun i p => scheduledSurvivorUnary (fun i : Σ a, Fin (size a) => role i.1)
              χ κ pivot n t i p *
            conj (scheduledSurvivorUnary (fun i : Σ a, Fin (size a) => role i.1)
              χ κ pivot n t' (e.symm i) p)) (fun i => (q i : ℕ)) *
        (groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
          childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ)) *
        conj (groupedFullCoprimeFourierWeight role n
          (fun v => (scheduleConstituentWord role size n v).map e)
          childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ))))
      else 0 := by
  have hpair : Pairwise (fun i j => (q (e i) : ℕ).Coprime (q (e j) : ℕ)) ↔
      Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) := by
    constructor
    · intro h i j hij
      simpa only [e.apply_symm_apply] using
        h (show e.symm i ≠ e.symm j from fun hh => hij (e.symm.injective hh))
    · intro h i j hij
      exact h (fun hh => hij (e.injective hh))
  have hleft := groupedFullCoprimeFourierWeight_atom role n (scheduleConstituentWord role size n)
    childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ))
  have hright := groupedFullCoprimeFourierWeight_atom role n
    (fun v => (scheduleConstituentWord role size n v).map e)
    childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ))
  simp only [List.map_map, Function.comp_def] at hright
  change groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
    childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ)) =
    fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      n (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) t at hleft
  change groupedFullCoprimeFourierWeight role n
    (fun v => (scheduleConstituentWord role size n v).map e)
    childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ)) =
    fullAtomTransferWeight role childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi)
      n (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q (e i) : ℕ))).prod) t' at hright
  unfold constituentPrimeTerm
  rw [hpair]
  by_cases hp : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ))
  · rw [ite_eq_left hp, map_mul, ite_eq_left hp, ite_eq_left hp, ← hleft, ← hright]
    have hh := scheduledSamplePhase_invariant_pair
      (fun i : Σ a, Fin (size a) => role i.1) χ κ pivot n t t' hroot e hχ P hP q hp center
    calc
      _ = (groupedFullCoprimeFourierWeight role n (scheduleConstituentWord role size n)
          childBound pivotBound ranges ψ X lo hi t (fun i => (q i : ℕ)) *
        conj (groupedFullCoprimeFourierWeight role n
          (fun v => (scheduleConstituentWord role size n v).map e)
          childBound pivotBound ranges ψ X lo hi t' (fun i => (q i : ℕ)))) *
        (scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1) χ κ pivot n t P hP q center *
          conj (scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
            χ κ pivot n t' P hP (fun i => q (e i)) center)) := by ring_nf; rfl
      _ = _ := by rw [hh]; ring
  · simp only [hp, ite_false, if_false, mul_zero, map_zero]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTopConditions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prime tests for a top atom pair containing a fixed pivot -/

namespace Ostmann

open scoped Classical

theorem TopPrimeCondition.fixPivot_holds {V : Type*} (M : ℕ)
    (c : TopPrimeCondition (Option V)) (hc : c.HasVariable) (x : V → ℕ) :
    (c.fixPivot M hc).Holds x ↔ c.Holds (fixedPivotPrimeValues M x) := by
  cases c with
  | distinct a b =>
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hc
      | some b =>
        exact Nat.coprime_comm
    | some a => cases b <;> rfl
  | external a N =>
    cases a with
    | none => exact False.elim hc
    | some a => rfl

theorem TopPrimeCondition.fixPivot_bounded {V : Type*} (M : ℕ) (R : ℝ) (hM : (M : ℝ) ≤ R)
    (c : TopPrimeCondition (Option V)) (hc : c.HasVariable) (hR : c.Bounded R) :
    (c.fixPivot M hc).Bounded R := by
  have hb : |((M : ℤ) : ℝ)| ≤ R := by
    simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ M from Nat.cast_nonneg M)] using hM
  cases c with
  | distinct a b =>
    cases a with
    | none =>
      cases b with
      | none => exact False.elim hc
      | some b => exact hb
    | some a =>
      cases b with
      | none => exact hb
      | some b => trivial
  | external a N =>
    cases a with
    | none => exact False.elim hc
    | some a => exact hR

theorem atomPairChecks_hasVariable {I V : Type*} [Fintype I]
    (words : I → List (Option V))
    (hunique : ∀ i j, none ∈ words i → none ∈ words j → i = j) :
    ∀ c ∈ atomPairChecks words, c.HasVariable := by
  intro c hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨j, _, hc⟩ := List.mem_flatMap.mp hc
  by_cases hij : i = j
  · simp only [hij, ite_true, if_true, List.not_mem_nil] at hc
  rw [ite_eq_right hij] at hc
  obtain ⟨v, hv, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  cases v <;> cases w
  · exact False.elim (hij (hunique i j hv hw))
  all_goals trivial

theorem fixedPivotCheckAt_all {V : Type*} (M : ℕ)
    (tests : List (TopPrimeCondition (Option V)))
    (h : ∀ c ∈ tests, c.HasVariable) (x : V → ℕ) :
    (∀ i, (fixedPivotCheckAt M tests h i).Holds x) ↔
      ∀ c ∈ tests, c.Holds (fixedPivotPrimeValues M x) := by
  constructor
  · intro hall c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
    exact (TopPrimeCondition.fixPivot_holds M _ _ x).mp (hall ⟨i, hi⟩)
  · intro hall i
    exact (TopPrimeCondition.fixPivot_holds M _ _ x).mpr (hall _ (List.getElem_mem i.isLt))

theorem fixedPivotCheckAt_bounded {V : Type*} (M : ℕ) (R : ℝ) (hM : (M : ℝ) ≤ R)
    (tests : List (TopPrimeCondition (Option V)))
    (h : ∀ c ∈ tests, c.HasVariable) (hR : ∀ c ∈ tests, c.Bounded R)
    (i : Fin tests.length) : (fixedPivotCheckAt M tests h i).Bounded R :=
  TopPrimeCondition.fixPivot_bounded M R hM _ _ (hR _ (List.getElem_mem i.isLt))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentPairFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact prime guard and counterpart mask in the actual matched pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituentPrimePairChecks_hasVariable (K : Type*) [Fintype K] :
    ∀ c ∈ constituentPrimePairChecks K, c.HasVariable := by
  apply atomPairChecks_hasVariable
  intro i j hi
  simp only [List.mem_singleton, reduceCtorEq] at hi

theorem constituentPrimePairChecks_iff {K : Type*} [Fintype K]
    (M : ℕ) (x : K → ℕ) :
    (∀ c ∈ constituentPrimePairChecks K, c.Holds (fixedPivotPrimeValues M x)) ↔
      Pairwise (fun i j => (x i).Coprime (x j)) := by
  simpa only [constituentPrimePairChecks, List.map_singleton, List.prod_singleton,
    fixedPivotPrimeValues] using
      (atomPairChecks_iff (fun i : K => [some i]) (fixedPivotPrimeValues M x))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotCoordinates
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every reconstructed prime check excludes the fixed pivot coordinate -/

namespace Ostmann

open scoped Classical

theorem reverseExpandedUnfixedCoordinates {I V : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (b : Bool) (pivot : ExpandedScheduledVariable (Option V) depth)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable (Option V) depth))
    (hc : ExpandedUnfixedCoordinates role depth (n + 1) current) :
    ExpandedUnfixedCoordinates role depth n (reverseCopyLabelMap role n b [pivot] current) := by
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

theorem mem_expandedOriginalWord_iff {V : Type*} {depth : ℕ}
    (w : List (ExpandedScheduledVariable V depth)) (v : V) :
    v ∈ expandedOriginalWord w ↔ Sum.inl v ∈ w := by
  induction w with
  | nil => simp [expandedOriginalWord]
  | cons a w ih => cases a <;> simp [expandedOriginalWord, ih]

theorem expandedYPrimeCoordinates_ne_none {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ)
    (current : CopyScheduleAtoms role (n + 1) → List (ExpandedScheduledVariable (Option V) depth))
    (hc : ExpandedUnfixedCoordinates role depth (n + 1) current) :
    ∀ v ∈ expandedYPrimeCoordinates role depth n current, v ≠ none := by
  intro v hv he
  subst v
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hv
  have hm := (mem_expandedOriginalWord_iff _ none).mp hi
  obtain ⟨a, ha⟩ := hc ⟨.inr i.val, i.property⟩
    (fun k => copyScheduleY_not_pivot role n i k) _ hm
  cases ha

theorem expandedSchedulePrimes_unfixed {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (depth n : ℕ) (path : List Bool)
    (current : CopyScheduleAtoms role n → List (ExpandedScheduledVariable (Option V) depth))
    (hc : ExpandedUnfixedCoordinates role depth n current) :
    (expandedSchedulePrimes role depth n path current).Coordinates (· ≠ none) := by
  induction n generalizing path with
  | zero => trivial
  | succ n ih =>
    exact ⟨expandedYPrimeCoordinates_ne_none role depth n current hc,
      ih (true :: path) _ (reverseExpandedUnfixedCoordinates role depth n true _ current hc),
      ih (false :: path) _ (reverseExpandedUnfixedCoordinates role depth n false _ current hc)⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotGraphEmbedding
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Embedding the retained graph while the pivot has only a constant coordinate -/

namespace Ostmann

open scoped BigOperators Classical

theorem fixedPivotUnary_norm {V : Type*} (ν : V → ℕ → ℂ)
    (hν : ∀ i p, ‖ν i p‖ ≤ 1) (i : Option V) (p : ℕ) :
    ‖fixedPivotUnary ν i p‖ ≤ 1 := by
  cases i
  · simp only [fixedPivotUnary, norm_one, le_refl]
  · exact hν _ _

theorem fixedPivotGraph_phase {V : Type*} [Fintype V]
    (χ : V → ∀ p : ℕ, DirichletCharacter ℂ p) (g : V → V → ℤ)
    (ν : V → ℕ → ℂ) (M : ℕ) (p : V → ℕ) :
    finiteEdgeWeight (dirichletGraphEdge (fixedPivotCharacters χ) (fixedPivotGraph g))
      (fixedPivotUnary ν) (fixedPivotPrimeValues M p) =
      finiteEdgeWeight (dirichletGraphEdge χ g) ν p := by
  simp only [finiteEdgeWeight, Fintype.prod_option, fixedPivotUnary, fixedPivotGraph,
    fixedPivotCharacters, dirichletGraphEdge, fixedPivotPrimeValues,
    zpow_zero, one_mul, mul_one, Finset.prod_const_one]
  congr 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_WordRootRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Adding one exact product cutoff at the root of a history -/

namespace Ostmann

open scoped BigOperators Classical

theorem WordRangeDecoration.prependRoot_count {σ : Type*} {n : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n) :
    (D.prependRoot r).count = D.count + 1 := by
  cases D with
  | leaf ranges => simp only [prependRoot, count, List.length_cons]
  | node ranges L R => simp only [prependRoot, count, List.length_cons]; omega

theorem WordRangeDecoration.prependRoot_bounded {σ : Type*} {n B : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n)
    (hr : r.word.length + 1 ≤ B) (hD : D.WordsBounded B) :
    (D.prependRoot r).WordsBounded B := by
  cases D with
  | leaf ranges =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hr
    · exact hD q hq
  | node ranges L R =>
    refine ⟨?_, hD.2.1, hD.2.2⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hr
    · exact hD.1 q hq

theorem WordRangeDecoration.prependRoot_formulas {σ : Type*} {n : ℕ}
    (r : WordRange σ) (D : WordRangeDecoration σ n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (env : σ → HistoryFormula σ) :
    (D.prependRoot r).formulas template t ht env =
      r.toHistory env :: D.formulas template t ht env := by
  cases template <;> cases D <;> rfl

theorem WordFourierParameters.primeUnitRangedCoefficient_prependRoot {V : Type*} {n : ℕ}
    (f : WordFourierParameters n) (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (r : WordRange (ExpandedScheduledVariable V n))
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    f.primeUnitRangedCoefficient C U (D.prependRoot r) template t ht x =
      (if (r.toHistory .prime).Holds (expandedPrimeValues n (fun i => (x i : ℤ))) then
        f.primeUnitRangedCoefficient C U D template t ht x else 0) := by
  simp only [primeUnitRangedCoefficient, unitRangedCoefficient, rangedCoefficient,
    WordRangeDecoration.prependRoot_formulas, List.forall_mem_cons]
  split_ifs <;> simp_all

/-- The finite correlation bound uses only the number of range tests, not
its endpoints. Thus the same bound applies uniformly to every root cutoff. -/
theorem rangedWordTransferPairBound_root_endpoints {σ : Type*} {n : ℕ}
    (template template' : WordTransferTemplate σ n) (D D' : WordRangeDecoration σ n)
    (r r' : WordRange σ) (t t' : FrequencyTree ℤ n)
    (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (f f' : WordFourierParameters n) (A E : ℕ)
    (P Q : Finset ℕ) (lower : ℝ) (Bq : ℕ) :
    rangedWordTransferPairBound template template' (D.prependRoot r) D' t t' ht ht' B f f' A E P Q lower Bq =
      rangedWordTransferPairBound template template' (D.prependRoot r') D' t t' ht ht' B f f' A E P Q lower Bq := by
  simp only [rangedWordTransferPairBound, WordRangeDecoration.prependRoot_count]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_OriginalProductRange
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root cutoffs for the product of specified original prime coordinates -/

namespace Ostmann

open scoped BigOperators Classical

theorem originalProductRange_holds {V : Type*} (w : List V) (n : ℕ) (lo hi : ℝ) (x : V → ℕ) :
    ((originalProductRange w n lo hi).toHistory .prime).Holds
        (expandedPrimeValues n (fun i => (x i : ℤ))) ↔
      lo ≤ ((w.map x).prod : ℝ) ∧ ((w.map x).prod : ℝ) ≤ hi := by
  have he := WordRange.toHistory_holds (originalProductRange w n lo hi) .prime
    (expandedPrimeValues n (fun i => (x i : ℤ))) (expandedPrimeNatValues n x)
    (by
      intro i
      cases i <;> simp only [HistoryFormula.value_prime, expandedPrimeValues,
        expandedPrimeNatValues, Int.cast_natCast, Int.cast_one, Nat.cast_one])
  rw [he]
  simp only [WordRange.Holds, originalProductRange, List.map_map, Function.comp_def,
    expandedPrimeNatValues, Set.mem_Icc]

theorem primeUnitRangedCoefficient_originalProductRange {V : Type*} {n : ℕ}
    (f : WordFourierParameters n) (C : WordPrimeDecoration V n)
    (U D : WordRangeDecoration (ExpandedScheduledVariable V n) n)
    (w : List V) (lo hi : ℝ)
    (template : WordTransferTemplate (ExpandedScheduledVariable V n) n)
    (t : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (x : V → ℕ) :
    f.primeUnitRangedCoefficient C U (D.prependRoot (originalProductRange w n lo hi)) template t ht x =
      if lo ≤ ((w.map x).prod : ℝ) ∧ ((w.map x).prod : ℝ) ≤ hi then
        f.primeUnitRangedCoefficient C U D template t ht x else 0 := by
  simpa only [originalProductRange_holds] using
    f.primeUnitRangedCoefficient_prependRoot C U D (originalProductRange w n lo hi) template t ht x

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Preliminaries_FiniteLayercake
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite positive layer decomposition for the diagonal ratio -/

namespace Ostmann

open scoped BigOperators Classical

/-- Uniform bounds on all upper level sums control every nonnegative bounded
multiplier with no loss depending on the number of sampled values. -/
theorem finite_level_sum_norm_bound {A : Type*} (S : Finset A)
    (r : A → ℝ) (c : A → ℂ) (M δ : ℝ)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hr : ∀ a ∈ S, 0 ≤ r a ∧ r a ≤ M)
    (hlevel : ∀ t : ℝ, 0 < t → ‖∑ a ∈ S, if t ≤ r a then c a else 0‖ ≤ δ) :
    ‖∑ a ∈ S, (r a : ℂ) * c a‖ ≤ M * δ := by
  revert r M
  refine Finset.strongInductionOn S ?_
  intro S ih r M hM hr hlevel
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha, hmin⟩ := S.exists_min_image r hS
    let m := r a
    have hm : 0 ≤ m := (hr a ha).1
    have hmM : m ≤ M := (hr a ha).2
    have herase : S.erase a ⊂ S := Finset.erase_ssubset ha
    have hr' : ∀ x ∈ S.erase a, 0 ≤ r x - m ∧ r x - m ≤ M - m := by
      intro x hx
      have hxS := Finset.mem_of_mem_erase hx
      exact ⟨sub_nonneg.mpr (hmin x hxS), sub_le_sub_right (hr x hxS).2 m⟩
    have hlevel' (t : ℝ) (ht : 0 < t) :
        ‖∑ x ∈ S.erase a, if t ≤ r x - m then c x else 0‖ ≤ δ := by
      have he : (∑ x ∈ S.erase a, if t ≤ r x - m then c x else 0) =
          ∑ x ∈ S, if t + m ≤ r x then c x else 0 := by
        rw [Finset.sum_erase_eq_sub ha]
        have heq (x : A) : (t ≤ r x - m) = (t + m ≤ r x) := propext (le_sub_iff_add_le)
        simp only [heq]
        have hno : ¬t + m ≤ r a := by dsimp [m]; linarith
        simp only [hno, ite_false, if_false, sub_zero]
      rw [he]
      exact hlevel (t + m) (add_pos_of_pos_of_nonneg ht hm)
    have hrest := ih (S.erase a) herase (fun x => r x - m) (M - m)
      (sub_nonneg.mpr hmM) hr' hlevel'
    have hfirst : ‖(m : ℂ) * ∑ x ∈ S, c x‖ ≤ m * δ := by
      by_cases hm0 : m = 0
      · simp only [hm0, Complex.ofReal_zero, zero_mul, norm_zero, le_refl]
      · have hmp : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
        have he : (∑ x ∈ S, if m ≤ r x then c x else 0) = ∑ x ∈ S, c x := by
          apply Finset.sum_congr rfl
          intro x hx
          exact ite_eq_left (hmin x hx)
        have hh := hlevel m hmp
        rw [he] at hh
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hm]
        exact mul_le_mul_of_nonneg_left hh hm
    have he : (∑ x ∈ S, (r x : ℂ) * c x) =
        (m : ℂ) * (∑ x ∈ S, c x) + ∑ x ∈ S.erase a, ((r x - m : ℝ) : ℂ) * c x := by
      rw [Finset.sum_erase_eq_sub ha]
      simp only [show r a - m = 0 from sub_self _, Complex.ofReal_zero, zero_mul, sub_zero,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      push_cast
      ring
    rw [he]
    calc
      _ ≤ ‖(m : ℂ) * ∑ x ∈ S, c x‖ + ‖∑ x ∈ S.erase a, ((r x - m : ℝ) : ℂ) * c x‖ := norm_add_le _ _
      _ ≤ m * δ + (M - m) * δ := add_le_add hfirst hrest
      _ = M * δ := by ring
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simpa only [Finset.sum_empty, norm_zero] using mul_nonneg hM hδ

/-- The normalized reciprocal product costs no additional constant once the
same correlation bound holds with arbitrary product upper cutoffs. -/
theorem finite_product_ratio_norm_bound {A : Type*} (S : Finset A)
    (H : A → ℝ) (c : A → ℂ) (X δ : ℝ) (hX : 0 < X) (hδ : 0 ≤ δ)
    (hH : ∀ a ∈ S, X ≤ H a)
    (hcut : ∀ R : ℝ, ‖∑ a ∈ S, if H a ≤ R then c a else 0‖ ≤ δ) :
    ‖∑ a ∈ S, ((X / H a : ℝ) : ℂ) * c a‖ ≤ δ := by
  have hp (a) (ha : a ∈ S) : 0 < H a := hX.trans_le (hH a ha)
  have hr : ∀ a ∈ S, 0 ≤ X / H a ∧ X / H a ≤ 1 := by
    intro a ha
    exact ⟨div_nonneg hX.le (hp a ha).le, (div_le_one (hp a ha)).mpr (hH a ha)⟩
  have hl (t : ℝ) (ht : 0 < t) :
      ‖∑ a ∈ S, if t ≤ X / H a then c a else 0‖ ≤ δ := by
    have he : (∑ a ∈ S, if t ≤ X / H a then c a else 0) =
        ∑ a ∈ S, if H a ≤ X / t then c a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hh : (t ≤ X / H a) = (H a ≤ X / t) := by
        apply propext
        rw [le_div_iff₀ (hp a ha), le_div_iff₀ ht, mul_comm t]
      simp only [hh]
    rw [he]
    exact hcut (X / t)
  simpa only [one_mul] using finite_level_sum_norm_bound S (fun a => X / H a) c 1 δ
    (by norm_num) hδ hr hl

/-- Zero coefficients can carry arbitrary product values. Only the original
supported terms need the lower product range. -/
theorem finite_product_ratio_norm_bound_on_support {A : Type*} (S : Finset A)
    (H : A → ℝ) (c : A → ℂ) (X δ : ℝ) (hX : 0 < X) (hδ : 0 ≤ δ)
    (hsupport : ∀ a ∈ S, c a ≠ 0 → X ≤ H a)
    (hcut : ∀ R : ℝ, ‖∑ a ∈ S, if H a ≤ R then c a else 0‖ ≤ δ) :
    ‖∑ a ∈ S, ((X / H a : ℝ) : ℂ) * c a‖ ≤ δ := by
  let S' := S.filter (fun a => X ≤ H a)
  have hz (a) (ha : a ∈ S) (hbad : ¬X ≤ H a) : c a = 0 := by
    by_contra hn
    exact hbad (hsupport a ha hn)
  have he (f : A → ℂ) : (∑ a ∈ S', f a * c a) = ∑ a ∈ S, f a * c a := by
    rw [show S' = S.filter (fun a => X ≤ H a) from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hh : X ≤ H a
    · simp only [hh, ite_true, if_true]
    · simp only [hh, ite_false, if_false, hz a ha hh, mul_zero]
  have hc (R : ℝ) : ‖∑ a ∈ S', if H a ≤ R then c a else 0‖ ≤ δ := by
    have he' : (∑ a ∈ S', if H a ≤ R then c a else 0) =
        ∑ a ∈ S, if H a ≤ R then c a else 0 := by
      simpa only [ite_mul, one_mul, zero_mul] using he (fun a => if H a ≤ R then 1 else 0)
    rw [he']
    exact hcut R
  rw [← he (fun a => ((X / H a : ℝ) : ℂ))]
  exact finite_product_ratio_norm_bound S' H c X δ hX hδ
    (fun _ ha => (Finset.mem_filter.mp ha).2) hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotRatioPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-prior cancellation with the normalized diagonal reciprocal -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem fixed_pivot_full_original_pair_ratio_bound {J : Type*} [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (a b : K) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : Option (K) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : Option (K) → Option (K) → ℤ)
    (unary : Option (K) → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph (some a) (some a) = 0 ∧ graph (some b) (some b) = 0) (hreverse : graph (some b) (some a) = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (some a) q ^ graph (some a) (some b) ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (checks : J → TopPrimeCondition (K))
    (hchecks : ∀ j, (checks j).Bounded R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (word : List (K)) (hword : word.length + 1 ≤ B)
    (X : ℝ) (hX : 0 < X)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' (D.prependRoot (originalProductRange (word.map some) n X 0)) D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let F : (K → P) → ℂ := fun x =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
          finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
          (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
            conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)
    ‖∑ x, ((X / ((word.map (fun i => (x i : ℕ))).prod : ℝ) : ℝ) : ℂ) *
      (if X ≤ ((word.map (fun i => (x i : ℕ))).prod : ℝ) then F x else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
        (α + Real.log R / V * α) := by
  let F : (K → P) → ℂ := fun x =>
    ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
        finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
        (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
          conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)
  let H : (K → P) → ℝ := fun x => ((word.map (fun i => (x i : ℕ))).prod : ℝ)
  let E0 := δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
    (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
    (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
    (α + Real.log R / V * α)
  have hE : 0 ≤ E0 := by
    have hf := pow_nonneg (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 f.profile from apply_nonneg _ _) (2 ^ n)
    have hf' := pow_nonneg (show 0 ≤ SchwartzMap.seminorm ℝ 0 0 f'.profile from apply_nonneg _ _) (2 ^ n)
    have hlog : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
    dsimp [E0]
    positivity
  have hc (R0 : ℝ) : ‖∑ x, if H x ≤ R0 then (if X ≤ H x then F x else 0) else 0‖ ≤ E0 := by
    have hDR := D.prependRoot_bounded (originalProductRange (word.map some) n X R0)
      (by simpa only [originalProductRange, List.length_map] using hword) hD
    have hnR : rangedWordTransferPairBound template template'
        (D.prependRoot (originalProductRange (word.map some) n X R0)) D' t t' ht ht' B f f'
        A E (Q b) (Q a) lower Bq ≤ δ ^ 2 := by
      rw [rangedWordTransferPairBound_root_endpoints template template' D D'
        (originalProductRange (word.map some) n X R0) (originalProductRange (word.map some) n X 0)]
      exact hnum
    have hh := fixed_pivot_full_original_pair_bound a b hab template template' C C' U U'
      (D.prependRoot (originalProductRange (word.map some) n X R0)) D' t t' ht ht' hC hC' B hB hwords hwords'
      hDR hD' hU hU' f f' χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass
      hnonprincipal A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
      α V R hα hV hR M hM hmax hlowerP hupperP checks hchecks hfreq hfreq' δ hδ hnR
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [primeUnitRangedCoefficient_originalProductRange]
    simp only [List.map_map, Function.comp_def, fixedPivotPrimeValues]
    dsimp only [F, H]
    split_ifs <;> simp_all <;> linarith
  exact finite_product_ratio_norm_bound_on_support Finset.univ H
    (fun x => if X ≤ H x then F x else 0) X E0 hX hE
    (by intro x _ hx; by_contra hn; simp only [hn, ite_false, if_false, ne_eq, not_true_eq_false] at hx)
    hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedGraphRatioPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap

theorem retained_graph_original_pair_ratio_bound {J : Type*} [Fintype J] {K : Type*} [Fintype K] [Nonempty K] {n : ℕ}
    (a b : K) (hab : a ≠ b)
    (template template' : WordTransferTemplate (ExpandedScheduledVariable (Option (K)) n) n)
    (C C' : WordPrimeDecoration (Option (K)) n)
    (U U' D D' : WordRangeDecoration (ExpandedScheduledVariable (Option (K)) n) n)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : C.Coordinates (· ≠ none)) (hC' : C'.Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) (hwords' : template'.WordsBounded B)
    (hD : D.WordsBounded B) (hD' : D'.WordsBounded B)
    (hU : U.WordsBounded B) (hU' : U'.WordsBounded B)
    (f f' : WordFourierParameters n)
    (χ : K → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : K → K → ℤ)
    (unary : K → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (checks : J → TopPrimeCondition (K))
    (hchecks : ∀ j, (checks j).Bounded R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (word : List (K)) (hword : word.length + 1 ≤ B)
    (X : ℝ) (hX : 0 < X)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound template template' (D.prependRoot (originalProductRange (word.map some) n X 0)) D' t t' ht ht' B f f'
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let F : (K → P) → ℂ := fun x =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if ∀ j, (checks j).Holds (fun i => (x i : ℕ)) then
          finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
          (f.primeUnitRangedCoefficient C U D template t ht (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
            conj (f'.primeUnitRangedCoefficient C' U' D' template' t' ht' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) else 0)
    ‖∑ x, ((X / ((word.map (fun i => (x i : ℕ))).prod : ℝ) : ℝ) : ℂ) *
      (if X ≤ ((word.map (fun i => (x i : ℕ))).prod : ℝ) then F x else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 f.profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 f'.profile) ^ (2 ^ n)) *
        (((C.count + C'.count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) + Fintype.card J) *
        (α + Real.log R / V * α) := by
  have hh := fixed_pivot_full_original_pair_ratio_bound a b hab template template'
    C C' U U' D D' t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU' f f'
    (fixedPivotCharacters χ) (fixedPivotGraph graph) (fixedPivotUnary unary)
    (fixedPivotUnary_norm unary hunary) hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR M hM hmax hlowerP hupperP checks hchecks hfreq hfreq' word hword X hX δ hδ hnum
  simpa only [fixedPivotGraph_phase] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedFixedPivotPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
variable (role : I → CopyScheduleRole) (n : ℕ)
variable (words words' : CopyScheduleAtoms role n → List (Option K))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

local notation "TplL" => expandedRootTemplate role n words childBound pivotBound
local notation "TplR" => expandedRootTemplate role n words' childBound pivotBound
local notation "PrL" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (words i))
local notation "PrR" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (words' i))
local notation "UrL" => expandedRootRanges role n words (totalAtomUnitRanges role)
local notation "UrR" => expandedRootRanges role n words' (totalAtomUnitRanges role)
local notation "DrL" => expandedRootRanges role n words ranges
local notation "DrR" => expandedRootRanges role n words' ranges
local notation "FP" => WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi

set_option maxHeartbeats 1600000 in
include hreal hu in
theorem grouped_fixed_pivot_original_ratio_bound
    (a b : K) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : (PrL).Coordinates (· ≠ none)) (hC' : (PrR).Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : (TplL).WordsBounded B) (hwords' : (TplR).WordsBounded B)
    (hD : (DrL).WordsBounded B) (hD' : (DrR).WordsBounded B)
    (hU : (UrL).WordsBounded B) (hU' : (UrR).WordsBounded B)
    (χ : K → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : K → K → ℤ)
    (unary : K → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (M : ℕ) (hM : (M : ℝ) ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (extra : List (TopPrimeCondition (Option K)))
    (hExtra : ∀ c ∈ extra, c.HasVariable) (hExtraR : ∀ c ∈ extra, c.Bounded R)
    (hLeft : ∀ c ∈ atomPairChecks words, c.HasVariable)
    (hRight : ∀ c ∈ atomPairChecks words', c.HasVariable)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (word : List (K)) (hword : word.length + 1 ≤ B)
    (Z : ℝ) (hZ : 0 < Z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound TplL TplR ((DrL).prependRoot (originalProductRange (word.map some) n Z 0)) DrR t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let q := fun x : K → P => fixedPivotPrimeValues M (fun i => (x i : ℕ))
    let G : (K → P) → ℂ := fun x =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if ∀ c ∈ extra, c.Holds (q x) then
          finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
            (groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t (q x) *
              conj (groupedFullCoprimeFourierWeight role n words' childBound pivotBound ranges ψ X lo hi t' (q x)))
        else 0)
    ‖∑ x, ((Z / ((word.map (fun i => (x i : ℕ))).prod : ℝ) : ℝ) : ℂ) *
      (if Z ≤ ((word.map (fun i => (x i : ℕ))).prod : ℝ) then G x else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
        ((((PrL).count + (PrR).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (extra ++ atomPairChecks words ++ atomPairChecks words').length) *
        (α + Real.log R / V * α) := by
  let tests := extra ++ atomPairChecks words ++ atomPairChecks words'
  have htests : ∀ c ∈ tests, c.HasVariable := by
    simpa only [tests, List.forall_mem_append] using ⟨⟨hExtra, hLeft⟩, hRight⟩
  have htestsR : ∀ c ∈ tests, c.Bounded R := by
    simpa only [tests, List.forall_mem_append] using
      ⟨⟨hExtraR, atomPairChecks_bounded words R⟩, atomPairChecks_bounded words' R⟩
  have hh := retained_graph_original_pair_ratio_bound a b hab TplL TplR PrL PrR UrL UrR DrL DrR
    t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU' FP FP
    χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR M hM hmax hlowerP hupperP
    (fixedPivotCheckAt M tests htests) (fixedPivotCheckAt_bounded M R hM tests htests htestsR)
    hfreq hfreq' word hword Z hZ δ hδ hnum
  dsimp only at hh ⊢
  rw [Fintype.card_fin] at hh
  simp_rw [fixedPivotCheckAt_all] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [groupedFullCoprimeFourierWeight_coefficient role n words childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi t ht _ hu,
    groupedFullCoprimeFourierWeight_coefficient role n words' childBound pivotBound ranges
      ψ hreal X lo hi hlo hhi t' ht' _ hu]
  simp only [tests, List.mem_append, or_imp, forall_and]
  split_ifs <;> simp_all

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_GroupedPrimePair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
variable (role : I → CopyScheduleRole) (n : ℕ)
variable (words words' : CopyScheduleAtoms role n → List (Option K))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

local notation "TplL" => expandedRootTemplate role n words childBound pivotBound
local notation "TplR" => expandedRootTemplate role n words' childBound pivotBound
local notation "PrL" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (words i))
local notation "PrR" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (words' i))
local notation "UrL" => expandedRootRanges role n words (totalAtomUnitRanges role)
local notation "UrR" => expandedRootRanges role n words' (totalAtomUnitRanges role)
local notation "DrL" => expandedRootRanges role n words ranges
local notation "DrR" => expandedRootRanges role n words' ranges
local notation "FP" => WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi

include hreal hu in
theorem grouped_prime_original_pair_bound
    (a b : K) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (hC : (PrL).Coordinates (· ≠ none)) (hC' : (PrR).Coordinates (· ≠ none))
    (B : ℕ) (hB : 1 ≤ B) (hwords : (TplL).WordsBounded B) (hwords' : (TplR).WordsBounded B)
    (hD : (DrL).WordsBounded B) (hD' : (DrR).WordsBounded B)
    (hU : (UrL).WordsBounded B) (hU' : (UrR).WordsBounded B)
    (χ : K → ∀ p : ℕ, DirichletCharacter ℂ p)
    (graph : K → K → ℤ)
    (unary : K → ℕ → ℂ) (hunary : ∀ i x, ‖unary i x‖ ≤ 1)
    (hself : graph a a = 0 ∧ graph b b = 0) (hreverse : graph b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ a q ^ graph a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (extra : List (TopPrimeCondition (Option K)))
    (hExtra : ∀ c ∈ extra, c.HasVariable) (hExtraR : ∀ c ∈ extra, c.Bounded R)
    (hLeft : ∀ c ∈ atomPairChecks words, c.HasVariable)
    (hRight : ∀ c ∈ atomPairChecks words', c.HasVariable)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound TplL TplR ((DrL).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) DrR t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let q := fun x : K → P => fixedPivotPrimeValues 1 (fun i => (x i : ℕ))
    let G : (K → P) → ℂ := fun x =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
        (if ∀ c ∈ extra, c.Holds (q x) then
          finiteEdgeWeight (dirichletGraphEdge χ graph) unary (fun i => (x i : ℕ)) *
            (groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t (q x) *
              conj (groupedFullCoprimeFourierWeight role n words' childBound pivotBound ranges ψ X lo hi t' (q x)))
        else 0)
    ‖∑ x, G x‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
        ((((PrL).count + (PrR).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (extra ++ atomPairChecks words ++ atomPairChecks words').length) *
        (α + Real.log R / V * α) := by
  have hh := grouped_fixed_pivot_original_ratio_bound role n words words'
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    a b hab t t' ht ht' hC hC' B hB hwords hwords' hD hD' hU hU'
    χ graph unary hunary hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR 1 (by norm_num; linarith) hmax hlowerP hupperP
    extra hExtra hExtraR hLeft hRight hfreq hfreq' [] (by simpa using hB)
    1 (by norm_num) δ hδ hnum
  dsimp only at hh ⊢
  simpa only [List.map_nil, List.prod_nil, Nat.cast_one, div_one, le_refl,
    ite_true, if_true, Complex.ofReal_one, one_mul] using hh

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_PrimeWordEmbedding
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The existing supported comparison specialized to words of actual primes -/

namespace Ostmann
open scoped Classical SchwartzMap FourierTransform

theorem primeWordEmbedding_unfixed {I K : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List K) :
    (expandedSchedulePrimes role n n []
      (fun i => (primeWordEmbedding words i).map Sum.inl)).Coordinates (· ≠ none) := by
  apply expandedSchedulePrimes_unfixed
  intro i _ v hv
  simp only [primeWordEmbedding, List.map_map, List.mem_map] at hv
  obtain ⟨a, _, rfl⟩ := hv
  exact ⟨a, rfl⟩

theorem primeWordEmbedding_hasVariable {I K : Type*} [Fintype I]
    (words : I → List K) :
    ∀ c ∈ atomPairChecks (primeWordEmbedding words), c.HasVariable := by
  apply atomPairChecks_hasVariable
  intro i j hi
  simp only [primeWordEmbedding, List.mem_map, Option.some_ne_none, and_false, exists_false] at hi

theorem groupedFullCoprimeFourierWeight_primeWordEmbedding {I K : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List K)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (p : K → ℕ) :
    groupedFullCoprimeFourierWeight role n (primeWordEmbedding words) childBound pivotBound
      ranges ψ X lo hi t (fixedPivotPrimeValues 1 p) =
    groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t p := by
  rw [groupedFullCoprimeFourierWeight_atom, groupedFullCoprimeFourierWeight_atom]
  congr 1
  funext i
  simp only [primeWordEmbedding, List.map_map, Function.comp_def, fixedPivotPrimeValues]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentFinalPairBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One-sided cancellation for the actual final fixed-history pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (SurvivingConstituent role size n))
variable (hχ : ∀ i, χ (copyScheduleOrigin n (e i).val) = χ (copyScheduleOrigin n i.val))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
local notation "K" => SurvivingConstituent role size n
local notation "ρ" => (fun i : Σ a, Fin (size a) => role (Sigma.fst i))
local notation "W" => primeWordEmbedding (scheduleConstituentWord role size n)
local notation "W'" => primeWordEmbedding (fun v => List.map e (scheduleConstituentWord role size n v))
local notation "G" => graphDifference (scheduledSurvivorGraph ρ pivot n)
  (transportGraph e (scheduledSurvivorGraph ρ pivot n))
local notation "Tpl" => expandedRootTemplate role n W childBound pivotBound
local notation "Tpl'" => expandedRootTemplate role n W' childBound pivotBound
local notation "D" => expandedRootRanges role n W ranges
local notation "D'" => expandedRootRanges role n W' ranges
local notation "U" => expandedRootRanges role n W (totalAtomUnitRanges role)
local notation "U'" => expandedRootRanges role n W' (totalAtomUnitRanges role)
local notation "Pr" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W i))
local notation "Pr'" => expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (W' i))
local notation "FP" => WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi

include hκ hχ hreal hu in
theorem constituent_final_pair_bound_oai
    (a b : K) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t)
    (ht' : NonzeroInternalFrequencies n t') (hroot : frequencyRoot n t = frequencyRoot n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : (Tpl).WordsBounded B) (hwords' : (Tpl').WordsBounded B)
    (hD : (D).WordsBounded B) (hD' : (D').WordsBounded B)
    (hU : (U).WordsBounded B) (hU' : (U').WordsBounded B) (hreverse : G b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : K → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, χ (copyScheduleOrigin n a.val) q ^ G a b ≠ 1)
    (A E : ℕ) (hA : 0 < A)
    (hMA : wordTransferFullPeriod n t B * wordTransferFullPeriod n t' B ≤ A)
    (hsmall : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t, 0 < s.natAbs ∧ s.natAbs < p)
    (hsmall' : ∀ p ∈ P, ∀ s ∈ allFrequencyList n t', 0 < s.natAbs ∧ s.natAbs < p)
    (hlow : ∀ p ∈ Q b, 2 * A ≤ p) (hhigh : ∀ p ∈ Q b, p ≤ E)
    (lower : ℝ) (hlower : 0 < lower) (hlowerQ : ∀ q ∈ Q a, lower ≤ (q : ℝ))
    (Bq : ℕ) (hBq : ∀ q : Q a, (q : ℕ) ≤ Bq)
    (α V R : ℝ) (hα : 0 ≤ α) (hV : 0 < V) (hR : 3 ≤ R)
    (hmax : ∀ i p, primeSubsetPrior P (Q i) p ≤ α)
    (hlowerP : ∀ p ∈ P, V ≤ Real.log (p : ℝ)) (hupperP : ∀ p ∈ P, (p : ℝ) ≤ R)
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound Tpl Tpl'
      ((D).prependRoot (originalProductRange ([] : List (Option K)) n 1 0)) D' t t' ht ht' B FP FP
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2)
    (center : ∀ p : ℕ, ZMod p) :
    ‖∑ q : K → P, ((∏ i, primeSubsetPrior P (Q i) (q i) : ℝ) : ℂ) *
      (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t q *
      conj (constituentPrimeTerm role size χ κ pivot n P hprime childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo hi) center t' (fun i => q (e i))))‖ ≤
    δ + ((SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n) *
      (SchwartzMap.seminorm ℝ 0 0 (FP).profile) ^ (2 ^ n)) *
      ((((Pr).count + (Pr').count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
        (constituentPrimePairChecks K ++ atomPairChecks W ++ atomPairChecks W').length) *
      (α + Real.log R / V * α) := by
  let : Nonempty K := ⟨a⟩
  have hself (i : K) : G i i = 0 := by
    simp only [graphDifference, transportGraph, scheduledSurvivorGraph,
      copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self, sub_self]
  have hn (i : K) (p : ℕ) :
      ‖scheduledSurvivorUnary ρ χ κ pivot n t i p *
        conj (scheduledSurvivorUnary ρ χ κ pivot n t' (e.symm i) p)‖ ≤ 1 := by
    apply graphQuotientUnary_norm
    · intro j q
      exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        (initialRegularUnary_norm_le_one χ κ hκ) n t j.val q
    · intro j q
      exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot (initialRegularUnary χ κ)
        (initialRegularUnary_norm_le_one χ κ hκ) n t' (e.symm j).val q
  have hh := grouped_prime_original_pair_bound role n W W' childBound pivotBound ranges
    ψ hreal X lo hi hlo hhi hu a b hab t t' ht ht'
    (primeWordEmbedding_unfixed role n _) (primeWordEmbedding_unfixed role n _)
    B hB hwords hwords' hD hD' hU hU'
    (fun i => χ (copyScheduleOrigin n i.val)) G
    (fun i p => scheduledSurvivorUnary ρ χ κ pivot n t i p *
      conj (scheduledSurvivorUnary ρ χ κ pivot n t' (e.symm i) p)) hn
    ⟨hself a, hself b⟩ hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR hmax hlowerP hupperP
    (constituentPrimePairChecks K) (constituentPrimePairChecks_hasVariable K)
    (atomPairChecks_bounded _ R) (primeWordEmbedding_hasVariable _) (primeWordEmbedding_hasVariable _)
    hfreq hfreq' δ hδ hnum
  dsimp only at hh
  simp_rw [constituentPrimePairChecks_iff,
    groupedFullCoprimeFourierWeight_primeWordEmbedding] at hh
  apply Eq.trans_le (congrArg norm ?_) hh
  apply Finset.sum_congr (by ext q; simp only [Finset.mem_univ])
  intro q _
  congr 1
  exact constituentPrimeTerm_pair role size χ κ pivot n P hprime childBound pivotBound ranges
    ψ X lo hi t t' hroot e hχ q center

end
end Ostmann

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Ostmann.constituent_final_pair_bound_oai.{u_1} := @OAI.Ostmann.constituent_final_pair_bound_oai.{u_1}
