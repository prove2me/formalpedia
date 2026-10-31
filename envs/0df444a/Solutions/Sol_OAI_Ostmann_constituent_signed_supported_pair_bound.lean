-- Prove2me | solution 1 for OAI.Ostmann.constituent_signed_supported_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:03:07.708738+00:00
-- url     : https://prove2.me/submissions/7c1f7d83-40a2-4559-beb7-071b10eaae1b

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ScheduledTransferGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restricting the graph update to the actual H/Y partition -/

namespace Ostmann

theorem scheduledRetainedGraph_diagonal {I : Type*} (role : I → CopyScheduleRole)
    (pivot : ℕ → I) (n : ℕ) (i : Option (CopyScheduleH role n ⊕ CopyScheduleY role n)) :
    scheduledRetainedGraph role initialCompleteGraph pivot n i i = 0 :=
  copyScheduleGraph_diagonal initialCompleteGraph pivot initialCompleteGraph_self n _

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteMatchedPrior
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The counterpart harmonic normalization on the actual finite slot type -/

namespace Ostmann

open scoped BigOperators Classical

theorem finite_enumeration_sum {A M : Type*} [AddCommMonoid M]
    (F G : Fintype A) (f : A → M) :
    Finset.sum (@Finset.univ A F) f = Finset.sum (@Finset.univ A G) f := by
  cases Subsingleton.elim F G
  rfl

theorem finite_matched_harmonic_prior {H : Type*} [Fintype H]
    (P : Finset ℕ) (Q : H → Finset ℕ) (e : Equiv.Perm H) (x : H → P) :
    (∏ i, primeSubsetPrior P (Q i) (x (e i))) =
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) * (∏ i, (x i : ℝ))⁻¹ *
        ∏ i, (if (x i : ℕ) ∈ Q (e.symm i) then (1 : ℝ) else 0) := by
  have hi (i : H) : primeSubsetPrior P (Q i) (x (e i)) =
      (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹ * (x (e i) : ℝ)⁻¹ *
        (if (x (e i) : ℕ) ∈ Q (e.symm (e i)) then (1 : ℝ) else 0) := by
    simp only [primeSubsetPrior, e.symm_apply_apply]
    split_ifs <;> simp only [mul_one, mul_zero]
    ring
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Equiv.prod_comp e (fun i => (x i : ℝ)⁻¹),
    Equiv.prod_comp e (fun i => if (x i : ℕ) ∈ Q (e.symm i) then (1 : ℝ) else 0),
    Finset.prod_inv_distrib]
  simp only [Finset.prod_inv_distrib]

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentCoreEnergy
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Unique-history energy of the actual fixed-pivot character core -/

namespace Ostmann
open scoped BigOperators Classical

theorem retainedGraphRow_norm_le_one {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (b : Option I → Option I → ℤ)
    (i : I) (M : ZMod p) (x : I → ZMod p) :
    ‖retainedGraphRow χ b i M x‖ ≤ 1 := by
  unfold retainedGraphRow
  rw [norm_mul, norm_prod]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul (character_zpow_norm_le_one _ _ _)
      (Finset.prod_le_one (fun _ _ => norm_nonneg _)
        (fun _ _ => character_zpow_norm_le_one _ _ _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := one_mul 1

theorem retainedCharacterBranch_norm_le_one {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νH : H → ℂ) (νY : Y → ℂ) (M : ℕ)
    (hH : ∀ h, ‖νH h‖ ≤ 1) (hY : ∀ y, ‖νY y‖ ≤ 1) :
    ‖retainedCharacterBranch L U χH χY b νH νY M‖ ≤ 1 := by
  unfold retainedCharacterBranch
  rw [norm_mul, norm_prod, norm_prod]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul ?_ ?_
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := one_mul 1
  · apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro h _
    rw [norm_mul]
    exact (mul_le_mul (hH h) (retainedGraphRow_norm_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans (one_mul 1).le
  · apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro y _
    rw [norm_mul]
    exact (mul_le_mul (hY y) (retainedGraphRow_norm_le_one _ _ _ _ _)
      (norm_nonneg _) zero_le_one).trans (one_mul 1).le

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
variable (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)

omit [Fintype D] in
include hP in
theorem constituentCharacterCore_norm_le_full (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) (d : D) :
    ‖constituentCharacterCore role size χ κ pivot n P hP childBound pivotBound ranges leaf hist u M (l, d)‖ ≤
      ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledInsertedAtoms role n M
          (fun h => ∏ k, (l (constituentH role size n h k) : ℕ))
          (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist d)‖ := by
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  unfold constituentCharacterCore
  rw [norm_mul]
  have hb := retainedCharacterBranch_norm_le_one (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
    (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val))
    (scheduledRetainedGraph (fun i : Σ a, Fin (size a) => role i.1) initialCompleteGraph pivot n)
    _ _ M
    (fun h => copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _
      (initialRegularUnary_norm_le_one χ κ hκ) n (hist d) h.val (l h))
    (fun y => copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _
      (initialRegularUnary_norm_le_one χ κ hκ) n (hist d) y.val (u y))
  apply (mul_le_of_le_one_right (norm_nonneg _) hb).trans
  unfold constituentUnweightedTransferWeight
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg _

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_MatchedRetainedPhase
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact diagonal phase quotients with a fixed external pivot -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem externalPivotUnary_norm_le_one {I : Type*}
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option I → Option I → ℤ) (ν : I → ℕ → ℂ) (M : ℕ)
    (hν : ∀ i p, ‖ν i p‖ ≤ 1) (i : I) (p : ℕ) :
    ‖externalPivotUnary χ b ν M i p‖ ≤ 1 := by
  rw [externalPivotUnary, norm_mul]
  exact (mul_le_mul (hν i p) (character_zpow_norm_le_one _ _ _)
    (norm_nonneg _) (by norm_num)).trans (by norm_num)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedCharacterGraph
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The matched character branch as its actual directed graph quotient -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem retainedCharacterBranch_eq_edge {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (χ : H ⊕ Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν : H ⊕ Y → ℕ → ℂ) (M : ℕ) :
    retainedCharacterBranch L U (fun h => χ (.inl h)) (fun y => χ (.inr y)) b
      (fun h => ν (.inl h) (L h)) (fun y => ν (.inr y) (U y)) M =
    finiteEdgeWeight (dirichletGraphEdge χ (retainedInternalGraph b))
      (externalPivotUnary χ b ν M) (Sum.elim L U) := by
  simp only [retainedCharacterBranch, finiteEdgeWeight, Fintype.prod_sum_type,
    externalPivotUnary, retainedInternalGraph, retainedGraphRow, dirichletGraphEdge,
    Sum.elim_inl, Sum.elim_inr, mul_assoc]
  congr 1

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentMatchedCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual supported character core in a matched diagonal pair -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate

theorem scheduledRetainedUnary_norm {I : Type*} (role : I → CopyScheduleRole)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (κ : I → ℕ → ℂ) (pivot : ℕ → I)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (n : ℕ) (t : FrequencyTree ℤ n)
    (i : CopyScheduleH role n ⊕ CopyScheduleY role n) (p : ℕ) :
    ‖scheduledRetainedUnary role χ κ pivot n t i p‖ ≤ 1 := by
  have hinit (i : I) (v : ℤ) (p : ℕ) : ‖initialRegularUnary χ κ i v p‖ ≤ 1 := by
    dsimp only [initialRegularUnary, regularUnary]
    rw [norm_mul]
    exact (mul_le_mul (hκ i p) (character_zpow_norm_le_one _ _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  cases i with
  | inl h => exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _ hinit n t h.val p
  | inr y => exact copyScheduleUnary_norm_le_one χ initialCompleteGraph pivot _ hinit n t y.val p

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_RetainedInvariantCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem retainedCharacterBranch_invariant_matching {H Y : Type*} [Fintype H] [Fintype Y]
    (L : H → ℕ) (U : Y → ℕ) [∀ h, Fact (L h).Prime] [∀ y, Fact (U y).Prime]
    (e : Equiv.Perm H) (χ : H ⊕ Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ h, χ (.inl (e h)) = χ (.inl h))
    (b c : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (ν ω : H ⊕ Y → ℕ → ℂ) (M : ℕ)
    (hp : Pairwise (fun i j => (Sum.elim L U i).Coprime (Sum.elim L U j)))
    (hb : ∀ i, b (some i) (some i) = 0) (hc : ∀ i, c (some i) (some i) = 0) :
    let : ∀ h, Fact ((L ∘ e) h).Prime := fun h => inferInstanceAs (Fact (L (e h)).Prime)
    let σ := Equiv.sumCongr e (Equiv.refl Y)
    retainedCharacterBranch L U (fun h => χ (.inl h)) (fun y => χ (.inr y)) b
      (fun h => ν (.inl h) (L h)) (fun y => ν (.inr y) (U y)) M *
      conj (retainedCharacterBranch (L ∘ e) U (fun h => χ (.inl h)) (fun y => χ (.inr y)) c
        (fun h => ω (.inl h) (L (e h))) (fun y => ω (.inr y) (U y)) M) =
    finiteEdgeWeight (dirichletGraphEdge χ
      (graphDifference (retainedInternalGraph b) (transportGraph σ (retainedInternalGraph c))))
      (fun i x => externalPivotUnary χ b ν M i x *
        conj (externalPivotUnary χ c ω M (σ.symm i) x)) (Sum.elim L U) := by
  let : ∀ h, Fact ((L ∘ e) h).Prime := fun h => inferInstanceAs (Fact (L (e h)).Prime)
  dsimp only
  let σ := Equiv.sumCongr e (Equiv.refl Y)
  have hσ (i) : χ (σ i) = χ i := by cases i with
    | inl h => exact hχ h
    | inr y => rfl
  rw [retainedCharacterBranch_eq_edge L U χ b ν M]
  have hr := retainedCharacterBranch_eq_edge (L ∘ e) U χ c ω M
  simp only [Function.comp_apply] at hr
  rw [hr]
  have he : Sum.elim (L ∘ e) U = Sum.elim L U ∘ σ := by
    funext i
    cases i <;> rfl
  rw [he, finiteEdgeWeight_invariant_transport σ χ hσ]
  exact dirichlet_graph_quotient χ (retainedInternalGraph b)
    (transportGraph σ (retainedInternalGraph c)) _ _ _ hp hb (fun i => hc (σ.symm i))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInvariantCharacter
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual original character signs survive every matching -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem constituentCharacterCore_invariant_matching {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
    (d d' : D) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let χR := scheduledRetainedCharacters ρ χ n
    let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY ρ n))
    let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
    let ν := scheduledRetainedUnary ρ χ κ pivot n (hist d)
    let ω := scheduledRetainedUnary ρ χ κ pivot n (hist d')
    constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges leaf hist u M (l ∘ e, d')) =
    (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l, d) *
      conj (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l ∘ e, d'))) *
    finiteEdgeWeight (dirichletGraphEdge χR
      (graphDifference (retainedInternalGraph g) (transportGraph σ (retainedInternalGraph g))))
      (fun i x => externalPivotUnary χR g ν M i x *
        conj (externalPivotUnary χR g ω M (σ.symm i) x))
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) := by
  dsimp only
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let χR := scheduledRetainedCharacters ρ χ n
  let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
  let ν := scheduledRetainedUnary ρ χ κ pivot n (hist d)
  let ω := scheduledRetainedUnary ρ χ κ pivot n (hist d')
  let : ∀ h, Fact (l h : ℕ).Prime := fun h => ⟨hP _ (l h).property⟩
  let : ∀ y, Fact (u y : ℕ).Prime := fun y => ⟨hP _ (u y).property⟩
  by_cases hp : Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j))
  · have he := retainedCharacterBranch_invariant_matching (fun h => (l h : ℕ))
      (fun y => (u y : ℕ)) e χR hχ g g ν ω M hp
      (fun i => scheduledRetainedGraph_diagonal ρ pivot n (some i))
      (fun i => scheduledRetainedGraph_diagonal ρ pivot n (some i))
    unfold constituentCharacterCore
    simp only [map_mul]
    calc
      _ = (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l, d) *
            conj (constituentUnweightedTransferWeight role size n P childBound pivotBound ranges leaf hist u M (l ∘ e, d'))) *
          (retainedCharacterBranch (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val)) g (fun h => ν (.inl h) (l h)) (fun y => ν (.inr y) (u y)) M *
          conj (retainedCharacterBranch (fun h => (l (e h) : ℕ)) (fun y => (u y : ℕ))
            (fun h => χ (copyScheduleOrigin n h.val)) (fun y => χ (copyScheduleOrigin n y.val)) g (fun h => ω (.inl h) (l (e h))) (fun y => ω (.inr y) (u y)) M)) := by
              dsimp only [ν, ω, scheduledRetainedUnary, χR, scheduledRetainedCharacters, Sum.elim_inl, Sum.elim_inr, g, ρ, Function.comp_apply]
              ring
      _ = _ := by
        congr 1
  · have hw : constituentUnweightedTransferWeight role size n P childBound pivotBound ranges
        leaf hist u M (l, d) = 0 := by
      unfold constituentUnweightedTransferWeight
      exact ite_eq_right hp
    unfold constituentCharacterCore
    rw [hw]
    simp only [zero_mul]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedConstituentWords
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Word coordinates for the fixed integer pivot and the retained primes -/

namespace Ostmann

open scoped BigOperators Classical

theorem insertedConstituentWord_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (v : CopyScheduleAtoms role n) :
    ((insertedConstituentWord role size n v).map (insertedConstituentValues role size n M l u)).prod =
      scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k)) v := by
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases a with p | h | y <;>
    simp only [insertedConstituentWord, scheduledInsertedAtoms, Equiv.symm_apply_apply,
      List.map_singleton, List.prod_singleton, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply, insertedConstituentValues]

theorem insertedConstituentValues_perm {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    insertedConstituentValues role size n M l u ∘ insertedConstituentPerm role size n e =
      insertedConstituentValues role size n M (l ∘ e) u := by
  funext v
  rcases v with _ | (h | y) <;> rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_InsertedConstituentFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual fixed-pivot weight in the supported word-Fourier coordinates -/

namespace Ostmann

open scoped BigOperators Classical SchwartzMap FourierTransform

theorem inserted_full_fourier_eq_grouped {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k))) t =
    groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
      childBound pivotBound ranges ψ X lo hi t (insertedConstituentValues role size n M l u) := by
  rw [groupedFullCoprimeFourierWeight_atom]
  congr 1
  funext v
  exact (insertedConstituentWord_prod role size n M l u v).symm

theorem inserted_full_fourier_permuted {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t : FrequencyTree ℤ n) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    fullAtomTransferWeight role childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, l (e (constituentH role size n h k)))
        (fun y => ∏ k, u (constituentY role size n y k))) t =
    groupedFullCoprimeFourierWeight role n
      (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
      childBound pivotBound ranges ψ X lo hi t (insertedConstituentValues role size n M l u) := by
  rw [groupedFullCoprimeFourierWeight_atom]
  congr 1
  funext v
  rw [List.map_map]
  rw [insertedConstituentValues_perm]
  exact (insertedConstituentWord_prod role size n M (l ∘ e) u v).symm

theorem constituentUnweighted_fourier_eq_grouped {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) :
    constituentUnweightedTransferWeight role size n P childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M a =
    if Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) then
      groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi (hist a.2)
        (insertedConstituentValues role size n M (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  unfold constituentUnweightedTransferWeight
  rw [inserted_full_fourier_eq_grouped role size n childBound pivotBound ranges ψ X lo hi
    (hist a.2) M (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ))]

theorem constituentUnweighted_permuted_fourier_eq_grouped {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (P : Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) (d : D) :
    constituentUnweightedTransferWeight role size n P childBound pivotBound ranges
      (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l ∘ e, d) =
    if Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)) then
      groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi (hist d)
        (insertedConstituentValues role size n M (fun h => (l h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n))
  let q := Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ))
  have he : Sum.elim (fun h => (l (e h) : ℕ)) (fun y => (u y : ℕ)) = q ∘ σ := by
    funext i
    cases i <;> rfl
  have hp : Pairwise (fun i j => (q (σ i)).Coprime (q (σ j))) ↔
      Pairwise (fun i j => (q i).Coprime (q j)) := by
    constructor
    · intro h i j hij
      simpa only [Equiv.apply_symm_apply] using h (σ.symm.injective.ne hij)
    · intro h i j hij
      exact h (σ.injective.ne hij)
  unfold constituentUnweightedTransferWeight
  simp only [Function.comp_apply, he]
  change (if Pairwise (fun i j => (q (σ i)).Coprime (q (σ j))) then _ else 0) = _
  rw [hp]
  congr 1
  exact inserted_full_fourier_permuted role size n childBound pivotBound ranges ψ X lo hi
    (hist d) M (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) e

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInvariantFourier
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituentCharacterCore_invariant_pair_fourier {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n))
    (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
    (d d' : D) :
    let ρ := fun i : Σ a, Fin (size a) => role i.1
    let χR := scheduledRetainedCharacters ρ χ n
    let σ := Equiv.sumCongr e (Equiv.refl (CopyScheduleY ρ n))
    let g := scheduledRetainedGraph ρ initialCompleteGraph pivot n
    let ν := scheduledRetainedUnary ρ χ κ pivot n (hist d)
    let ω := scheduledRetainedUnary ρ χ κ pivot n (hist d')
    constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l, d) *
      conj (constituentCharacterCore role size χ κ pivot n P hP
        childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M (l ∘ e, d')) =
    if Pairwise (fun i j =>
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)) j)) then
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
          childBound pivotBound ranges ψ X lo hi (hist d)
          (insertedConstituentValues role size n M (fun h => (l h : ℕ)) (fun y => (u y : ℕ))) *
        conj (groupedFullCoprimeFourierWeight role n
          (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
          childBound pivotBound ranges ψ X lo hi (hist d')
          (insertedConstituentValues role size n M (fun h => (l h : ℕ)) (fun y => (u y : ℕ))))) *
    finiteEdgeWeight (dirichletGraphEdge χR
      (graphDifference (retainedInternalGraph g) (transportGraph σ (retainedInternalGraph g))))
      (fun i x => externalPivotUnary χR g ν M i x *
        conj (externalPivotUnary χR g ω M (σ.symm i) x))
      (Sum.elim (fun h => (l h : ℕ)) (fun y => (u y : ℕ)))
    else 0 := by
  have h := constituentCharacterCore_invariant_matching role size χ κ pivot n P hP
    childBound pivotBound ranges (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) * normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)) hist u M l e hχ d d'
  dsimp only at h ⊢
  rw [constituentUnweighted_fourier_eq_grouped,
    constituentUnweighted_permuted_fourier_eq_grouped] at h
  split_ifs at h ⊢ with hp
  · exact h
  · simpa only [map_zero, zero_mul] using h

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FixedPivotTopConditions
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem insertedConstituentWord_none {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n)
    (hv : none ∈ insertedConstituentWord role size n v) :
    ∃ p : CurrentPivotConstituent role n, v = scheduledPartitionEquiv role n (.inl p) := by
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases a with p | h | y
  · exact ⟨p, rfl⟩
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_ofFn] at hv
    obtain ⟨k, hk⟩ := hv
    cases hk
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_ofFn] at hv
    obtain ⟨k, hk⟩ := hv
    cases hk

theorem insertedConstituentWord_none_unique {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b)
    (v w : CopyScheduleAtoms role n)
    (hv : none ∈ insertedConstituentWord role size n v)
    (hw : none ∈ insertedConstituentWord role size n w) : v = w := by
  obtain ⟨p, rfl⟩ := insertedConstituentWord_none role size n v hv
  obtain ⟨q, rfl⟩ := insertedConstituentWord_none role size n w hw
  have hpq : p = q := Subtype.ext (hu p.val q.val p.property q.property)
  rw [hpq]

theorem insertedAtomPairChecks_hasVariable {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b) :
    ∀ c ∈ atomPairChecks (insertedConstituentWord role size n), c.HasVariable :=
  atomPairChecks_hasVariable _ (insertedConstituentWord_none_unique role size n hu)

theorem none_mem_option_map_iff {V : Type*} (e : Equiv.Perm V) (w : List (Option V)) :
    none ∈ w.map (Equiv.optionCongr e) ↔ none ∈ w := by
  constructor
  · intro h
    obtain ⟨v, hv, he⟩ := List.mem_map.mp h
    cases v with
    | none => exact hv
    | some v => cases he
  · intro h
    exact List.mem_map.mpr ⟨none, h, rfl⟩

theorem insertedPermutedAtomPairChecks_hasVariable {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (hu : ∀ a b, role a = .pivot n → role b = .pivot n → a = b)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    ∀ c ∈ atomPairChecks (fun i =>
      (insertedConstituentWord role size n i).map (insertedConstituentPerm role size n e)),
      c.HasVariable := by
  apply atomPairChecks_hasVariable
  intro i j hi hj
  apply insertedConstituentWord_none_unique role size n hu i j
  · exact (none_mem_option_map_iff _ _).mp hi
  · exact (none_mem_option_map_iff _ _).mp hj

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
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
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

theorem finiteEdgeWeight_mul_unary {K : Type*} [Fintype K]
    (E : K → K → ℕ → ℕ → ℂ) (η ν : K → ℕ → ℂ) (x : K → ℕ) :
    (∏ i, η i (x i)) * finiteEdgeWeight E ν x =
      finiteEdgeWeight E (fun i p => η i p * ν i p) x := by
  simp only [finiteEdgeWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem constituentCounterpartMask_norm {H Y : Type*}
    (Q : H → Finset ℕ) (e : Equiv.Perm H) (i : H ⊕ Y) (p : ℕ) :
    ‖constituentCounterpartMask Q e i p‖ ≤ 1 := by
  cases i <;> simp only [constituentCounterpartMask]
  · split_ifs <;> norm_num
  · norm_num

theorem constituentCounterpartMask_prod {H Y : Type*} [Fintype H] [Fintype Y]
    (Q : H → Finset ℕ) (e : Equiv.Perm H) (x : H ⊕ Y → ℕ) :
    (∏ i, constituentCounterpartMask Q e i (x i)) =
      ((∏ h, if x (.inl h) ∈ Q (e.symm h) then (1 : ℝ) else 0) : ℂ) := by
  rw [Fintype.prod_sum_type]
  simp only [constituentCounterpartMask, Finset.prod_const_one, mul_one,
    Complex.ofReal_one]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentInvariantPairFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original conjugate-role characters in the exact masked pair -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform
section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ)

omit [Fintype I] in
theorem constituentInvariantUnary_norm (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) (Q : (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) → Finset ℕ) (M : ℕ)
    (t t' : FrequencyTree ℤ n) (i : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (p : ℕ) :
    ‖constituentInvariantUnary role size χ κ pivot n e Q M t t' i p‖ ≤ 1 := by
  have hh (s : FrequencyTree ℤ n) (i : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) :
      ‖externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) (scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n)
        (scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n s) M i p‖ ≤ 1 :=
    externalPivotUnary_norm_le_one _ _ _ M
      (scheduledRetainedUnary_norm ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot hκ n s) i p
  unfold constituentInvariantUnary
  rw [norm_mul, norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * (1 * 1) := mul_le_mul (constituentCounterpartMask_norm Q e i p)
      (mul_le_mul (hh t i) (hh t' _) (norm_nonneg _) (by norm_num))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 1 := by norm_num

theorem constituentMaskedPair_invariant_fourier (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (t t' : FrequencyTree ℤ n)
    (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
    (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
    (Q : (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) → Finset ℕ) (M : ℕ) (x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := constituentCharacterCore role size χ κ pivot n P hP
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    ((∏ h, if (x (.inl h) : ℕ) ∈ Q (e.symm h) then (1 : ℝ) else 0) : ℂ) *
      (core ((fun h => x (.inl h)), t) * conj (core ((fun h => x (.inl (e h))), t'))) =
    if ∀ c ∈ constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)), c.Holds (fixedPivotPrimeValues M (fun i => (x i : ℕ))) then
      finiteEdgeWeight (dirichletGraphEdge (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) (constituentMatchedGraph role size pivot n e))
        (constituentInvariantUnary role size χ κ pivot n e Q M t t') (fun i => (x i : ℕ)) *
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi t (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
      conj (groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi t' (fixedPivotPrimeValues M (fun i => (x i : ℕ)))))
    else 0 := by
  dsimp only
  simp only [constituentPrimePairChecks_iff]
  have hx : Sum.elim (fun h => (x (.inl h) : ℕ)) (fun y => (x (.inr y) : ℕ)) =
      (fun i => (x i : ℕ)) := by funext i; cases i <;> rfl
  have hv : insertedConstituentValues role size n M (fun h => (x (.inl h) : ℕ))
      (fun y => (x (.inr y) : ℕ)) = fixedPivotPrimeValues M (fun i => (x i : ℕ)) := by
    funext i; rcases i with _ | (h | y) <;> rfl
  have hp := constituentCharacterCore_invariant_pair_fourier role size χ κ pivot n P hP
    childBound pivotBound ranges ψ X lo hi (fun z : FrequencyTree ℤ n => z)
    (fun y => x (.inr y)) M (fun h => x (.inl h)) e hχ t t'
  simp only [hx, hv] at hp
  trans (∏ h, if (x (.inl h) : ℕ) ∈ Q (e.symm h) then (1 : ℝ) else 0 : ℂ) *
    (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) then
      (groupedFullCoprimeFourierWeight role n (insertedConstituentWord role size n)
        childBound pivotBound ranges ψ X lo hi t (fixedPivotPrimeValues M (fun i => (x i : ℕ))) *
      conj (groupedFullCoprimeFourierWeight role n
        (fun v => (insertedConstituentWord role size n v).map (insertedConstituentPerm role size n e))
        childBound pivotBound ranges ψ X lo hi t' (fixedPivotPrimeValues M (fun i => (x i : ℕ))))) *
      finiteEdgeWeight (dirichletGraphEdge (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n) (constituentMatchedGraph role size pivot n e))
        (fun i p => externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n)
          (scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n)
          (scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t) M i p *
          conj (externalPivotUnary (scheduledRetainedCharacters ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ n)
            (scheduledRetainedGraph ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) initialCompleteGraph pivot n)
            (scheduledRetainedUnary ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) χ κ pivot n t') M
            ((Equiv.sumCongr e (Equiv.refl (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))).symm i) p)) (fun i => (x i : ℕ))
    else 0)
  · congr 1
  split_ifs
  · rw [← constituentCounterpartMask_prod Q e (fun i => (x i : ℕ))]
    unfold constituentMatchedGraph constituentInvariantUnary
    conv_rhs => rw [← finiteEdgeWeight_mul_unary]
    ring
  · simp only [mul_zero]

end
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

theorem inserted_root_unfixed_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) :
    ExpandedUnfixedCoordinates role n n
      (fun i => (insertedConstituentWord role size n i).map Sum.inl) := by
  intro i hi v hv
  obtain ⟨a, rfl⟩ := (scheduledPartitionEquiv role n).surjective i
  rcases a with p | h | y
  · exact False.elim (hi n (copyScheduleRole_positive role p.val n p.property n))
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_map, List.mem_ofFn] at hv
    obtain ⟨z, ⟨k, rfl⟩, rfl⟩ := hv
    exact ⟨.inl (constituentH role size n h k), rfl⟩
  · simp only [insertedConstituentWord, Equiv.symm_apply_apply, List.mem_map, List.mem_ofFn] at hv
    obtain ⟨z, ⟨k, rfl⟩, rfl⟩ := hv
    exact ⟨.inr (constituentY role size n y k), rfl⟩

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

theorem insertedSchedulePrimes_unfixed {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) :
    (expandedSchedulePrimes role n n []
      (fun i => (insertedConstituentWord role size n i).map Sum.inl)).Coordinates (· ≠ none) :=
  expandedSchedulePrimes_unfixed role n n [] _ (inserted_root_unfixed_coordinates role size n)

theorem inserted_permuted_root_unfixed_coordinates {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    ExpandedUnfixedCoordinates role n n (fun i =>
      ((insertedConstituentWord role size n i).map
        (insertedConstituentPerm role size n e)).map Sum.inl) := by
  intro i hi v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
  have hroot := inserted_root_unfixed_coordinates role size n i hi (.inl z)
    (List.mem_map.mpr ⟨z, hz, rfl⟩)
  obtain ⟨a, ha⟩ := hroot
  have hza : z = some a := Sum.inl.inj ha
  subst z
  exact ⟨_, rfl⟩

theorem insertedPermutedSchedulePrimes_unfixed {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (e : Equiv.Perm (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n)) :
    (expandedSchedulePrimes role n n [] (fun i =>
      ((insertedConstituentWord role size n i).map
        (insertedConstituentPerm role size n e)).map Sum.inl)).Coordinates (· ≠ none) :=
  expandedSchedulePrimes_unfixed role n n [] _
    (inserted_permuted_root_unfixed_coordinates role size n e)

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
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSignedPairRatio
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-sided estimate for the actual masked constituent pair -/

namespace Ostmann
open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
variable (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

include hreal hu hκ hχ in
theorem constituent_signed_pair_ratio_bound
    (a b : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : ((expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound)).WordsBounded B) (hwordsR : ((expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound)).WordsBounded B)
    (hD : ((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).WordsBounded B) (hD' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges)).WordsBounded B)
    (hU : ((expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role))).WordsBounded B) (hU' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role))).WordsBounded B)
    (hself : ((constituentMatchedGraph role size pivot n e)) a a = 0 ∧ ((constituentMatchedGraph role size pivot n e)) b b = 0) (hreverse : ((constituentMatchedGraph role size pivot n e)) b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, ((scheduledRetainedCharacters (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) χ n) a q) ^ ((constituentMatchedGraph role size pivot n e)) a b ≠ 1)
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
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (word : List (((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)))) (hword : word.length + 1 ≤ B)
    (Z : ℝ) (hZ : 0 < Z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound) (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound) (((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).prependRoot (originalProductRange (word.map some) n Z 0)) (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges) t t' ht ht' B (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi) (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := fun x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P => constituentCharacterCore role size χ κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    let G := fun x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P =>
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) *
        (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t'))))
    ‖∑ x, ((Z / ((word.map (fun i => (x i : ℕ))).prod : ℝ) : ℝ) : ℂ) *
      (if Z ≤ ((word.map (fun i => (x i : ℕ))).prod : ℝ) then G x else 0)‖ ≤
      δ + ((SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n)) *
        (((((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i)))).count + ((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i)))).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length) *
        (α + Real.log R / V * α) := by
  let : Nonempty ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) := ⟨a⟩
  have hh := grouped_fixed_pivot_original_ratio_bound role n (insertedConstituentWord role size n) ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi
    (fun j hj => hu j (Nat.le_of_lt hj)) a b hab t t' ht ht'
    (insertedSchedulePrimes_unfixed role size n) (insertedPermutedSchedulePrimes_unfixed role size n e)
    B hB hwords hwordsR hD hD' hU hU' (scheduledRetainedCharacters (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) χ n) (constituentMatchedGraph role size pivot n e)
    (constituentInvariantUnary role size χ κ pivot n e (fun h => Q (.inl h)) M t t')
    (constituentInvariantUnary_norm role size χ κ pivot n hκ e (fun h => Q (.inl h)) M t t')
    hself hreverse P hP hprime Q hQP hQmass hnonprincipal
    A E hA hMA hsmall hsmall' hlow hhigh lower hlower hlowerQ Bq hBq
    α V R hα hV hR M hM hmax hlowerP hupperP
    (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (constituentPrimePairChecks_hasVariable ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)))
    (atomPairChecks_bounded _ R)
    (insertedAtomPairChecks_hasVariable role size n (hu n le_rfl))
    (insertedPermutedAtomPairChecks_hasVariable role size n (hu n le_rfl) e)
    hfreq hfreq' word hword Z hZ δ hδ hnum
  dsimp only at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  refine Finset.sum_congr (by ext x; simp only [Finset.mem_univ]) ?_
  intro x _
  congr 2
  apply congrArg (fun z : ℂ => ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) * z)
  exact constituentMaskedPair_invariant_fourier role size χ κ pivot n P hprime
    childBound pivotBound ranges ψ X lo hi t t' e hχ (fun h => Q (.inl h)) M x

end
end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteMatchedWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counterpart normalization on the original H and Y product law -/

namespace Ostmann
open scoped BigOperators Classical

theorem retainedHWord_length (H Y : Type*) [Fintype H] :
    (retainedHWord H Y).length = Fintype.card H := by
  simp only [retainedHWord, List.length_map, Finset.length_toList, Finset.card_univ]

theorem retainedHWord_prod {H Y : Type*} [Fintype H] (x : H ⊕ Y → ℕ) :
    ((retainedHWord H Y).map x).prod = ∏ h, x (.inl h) := by
  simp only [retainedHWord, List.map_map, Finset.prod_map_toList, Function.comp_apply]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_FiniteMatchedSupportedWindow
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counterpart normalization on the live coefficient support -/
namespace Ostmann
open scoped Classical BigOperators

theorem finite_matched_supported_window_eq {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ)
    (Z : ℝ) (hZ : 0 < Z) (hscale : ∀ x, F x ≠ 0 → Z ≤ ∏ h, (x (.inl h) : ℝ)) :
    (∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x) =
    (((∏ h, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ : ℝ) : ℂ) *
      ∑ x : H ⊕ Y → P, ((Z / (∏ h, (x (.inl h) : ℝ)) : ℝ) : ℂ) *
        (if Z ≤ ∏ h, (x (.inl h) : ℝ) then
          ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
          (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) * F x)
        else 0) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hF : F x = 0
  · simp only [hF, mul_zero, ite_self]
  by_cases hx : (∏ i, primeSubsetPrior P (Q i) (x i)) = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
    split_ifs <;> simp only [mul_zero]
  · have hs := hscale x hF
    rw [ite_eq_left hs, finite_matched_harmonic_prior P (fun h => Q (.inl h)) e
      (fun h => x (.inl h))]
    have he (C D U : ℝ) : C * D⁻¹ * U = (C * Z⁻¹) * (Z / D) * U := by
      rw [div_eq_mul_inv]
      field_simp
    rw [he]
    push_cast
    simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
    ring

theorem finite_matched_supported_window_bound {H Y : Type*} [Fintype H] [Fintype Y]
    (P : Finset ℕ) (Q : H ⊕ Y → Finset ℕ) (e : Equiv.Perm H)
    (F : (H ⊕ Y → P) → ℂ)
    (Z : ℝ) (hZ : 0 < Z) (hscale : ∀ x, F x ≠ 0 → Z ≤ ∏ h, (x (.inl h) : ℝ)) (δ : ℝ)
    (hbound : ‖∑ x : H ⊕ Y → P, ((Z / (∏ h, (x (.inl h) : ℝ)) : ℝ) : ℂ) *
        (if Z ≤ ∏ h, (x (.inl h) : ℝ) then
          ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
          (((∏ h, if (x (.inl h) : ℕ) ∈ Q (.inl (e.symm h)) then (1 : ℝ) else 0) : ℂ) * F x)
        else 0)‖ ≤ δ) :
    ‖∑ x : H ⊕ Y → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) * F x‖ ≤
        (∏ h, (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ * δ := by
  rw [finite_matched_supported_window_eq P Q e F Z hZ hscale, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Construction_ConstituentSignedSupportedPair
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The matched correlation under both original harmonic priors -/

namespace Ostmann
open scoped BigOperators ComplexConjugate Classical SchwartzMap FourierTransform

section
variable {I : Type*} [Fintype I]
variable (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
variable (e : Equiv.Perm (CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))
variable (hχ : ∀ h, χ (copyScheduleOrigin n (e h).val) = χ (copyScheduleOrigin n h.val))
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (ψ : 𝓢(ℝ, ℂ)) (hreal : ∀ y, conj (ψ y) = ψ y)
variable (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
variable (hu : ∀ j ≤ n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)

include hreal hu hκ hχ in
theorem constituent_signed_supported_pair_bound_oai
    (a b : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n))) (hab : a ≠ b)
    (t t' : FrequencyTree ℤ n) (ht : NonzeroInternalFrequencies n t) (ht' : NonzeroInternalFrequencies n t')
    (B : ℕ) (hB : 1 ≤ B) (hwords : ((expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound)).WordsBounded B) (hwordsR : ((expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound)).WordsBounded B)
    (hD : ((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).WordsBounded B) (hD' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges)).WordsBounded B)
    (hU : ((expandedRootRanges role n (insertedConstituentWord role size n) (totalAtomUnitRanges role))).WordsBounded B) (hU' : ((expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) (totalAtomUnitRanges role))).WordsBounded B)
    (hself : ((constituentMatchedGraph role size pivot n e)) a a = 0 ∧ ((constituentMatchedGraph role size pivot n e)) b b = 0) (hreverse : ((constituentMatchedGraph role size pivot n e)) b a = 0)
    (P : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (Q : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQmass : ∀ i, 0 < ∑ q ∈ Q i, (q : ℝ)⁻¹)
    (hnonprincipal : ∀ q ∈ Q a, ((scheduledRetainedCharacters (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) χ n) a q) ^ ((constituentMatchedGraph role size pivot n e)) a b ≠ 1)
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
    (hfreq : ∀ s ∈ allFrequencyList n t, |(s : ℝ)| ≤ R)
    (hfreq' : ∀ s ∈ allFrequencyList n t', |(s : ℝ)| ≤ R)
    (hword : Fintype.card (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) + 1 ≤ B)
    (Z : ℝ) (hZ : 0 < Z)
    (hproduct : ConstituentHProductLower role size n childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) Z)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hnum : rangedWordTransferPairBound (expandedRootTemplate role n (insertedConstituentWord role size n) childBound pivotBound) (expandedRootTemplate role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) childBound pivotBound) (((expandedRootRanges role n (insertedConstituentWord role size n) ranges)).prependRoot (originalProductRange ((retainedHWord (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n)).map some) n Z 0)) (expandedRootRanges role n ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) ranges) t t' ht ht' B (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi) (WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)
      A E (Q b) (Q a) lower Bq ≤ δ ^ 2) :
    let leaf := fun τ (v : ℤ) => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
      normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X)
    let core := fun x : ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) → P => constituentCharacterCore role size χ κ pivot n P hprime
      childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z) (fun y => x (.inr y)) M
    ‖∑ x : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) ⊕ (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ((∏ h, primeSubsetPrior P (Q (.inl h)) (x (.inl (e h))) : ℝ) : ℂ) *
      (core x ((fun h => x (.inl h)), t) * conj (core x ((fun h => x (.inl (e h))), t')))‖ ≤
      (∏ h : (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n), (∑ p ∈ Q (.inl h), (p : ℝ)⁻¹)⁻¹) * Z⁻¹ *
      (δ + ((SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n) *
        (SchwartzMap.seminorm ℝ 0 0 ((WordFourierParameters.uniform n (𝓕 ψ : 𝓢(ℝ, ℂ)) X lo hi hlo hhi)).profile) ^ (2 ^ n)) *
        (((((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl ((insertedConstituentWord role size n) i)))).count + ((expandedSchedulePrimes role n n [] (fun i => List.map Sum.inl (((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i))) i)))).count : ℕ) : ℝ) * (B ^ (n + 1) : ℕ) +
          (constituentPrimePairChecks ((CopyScheduleH ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n) ⊕ (CopyScheduleY ((fun i : Σ a, Fin (size a) => role (Sigma.fst i))) n)) ++ atomPairChecks (insertedConstituentWord role size n) ++ atomPairChecks ((fun i => List.map (insertedConstituentPerm role size n e) ((insertedConstituentWord role size n) i)))).length) *
        (α + Real.log R / V * α)) := by
  extract_lets leaf core
  refine Eq.trans_le (congrArg norm (finite_enumeration_sum _ _ _))
    (finite_matched_supported_window_bound P Q e
    (fun x => core x ((fun h => x (.inl h)), t) *
      conj (core x ((fun h => x (.inl (e h))), t'))) Z hZ (by
      intro x hx
      have hc := (mul_ne_zero_iff.mp hx).1
      have hf := (norm_pos_iff.mpr hc).trans_le
        (constituentCharacterCore_norm_le_full role size χ κ pivot n P hprime
          childBound pivotBound ranges leaf (fun z : FrequencyTree ℤ n => z)
          (fun y => x (.inr y)) M hκ (fun h => x (.inl h)) t)
      exact hproduct M t (fun h => (x (.inl h) : ℕ))
        (fun y => (x (.inr y) : ℕ)) (norm_pos_iff.mp hf)) _ ?_)
  have hh := constituent_signed_pair_ratio_bound role size n χ κ pivot hκ e hχ
    childBound pivotBound ranges ψ hreal X lo hi hlo hhi hu
    a b hab t t' ht ht' B hB hwords hwordsR hD hD' hU hU' hself hreverse
    P hP hprime Q hQP hQmass hnonprincipal A E hA hMA hsmall hsmall'
    hlow hhigh lower hlower hlowerQ Bq hBq α V R hα hV hR M hM hmax hlowerP hupperP
    hfreq hfreq' (retainedHWord (CopyScheduleH (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n) (CopyScheduleY (fun i : Σ a, Fin (size a) => role (Sigma.fst i)) n)) (by simpa only [retainedHWord_length] using hword) Z hZ δ hδ hnum
  dsimp only at hh
  simp only [retainedHWord_prod, Nat.cast_prod] at hh
  exact Eq.trans_le (congrArg norm (finite_enumeration_sum _ _ _)) hh

end
end Ostmann

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Ostmann.constituent_signed_supported_pair_bound_oai.{u_1} := @OAI.Ostmann.constituent_signed_supported_pair_bound_oai.{u_1}
