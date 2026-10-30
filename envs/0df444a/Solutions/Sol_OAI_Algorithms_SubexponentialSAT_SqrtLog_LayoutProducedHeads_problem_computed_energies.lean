-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:27:26.767979+00:00
-- url     : https://prove2.me/submissions/7191e186-75e1-46d0-b6a0-079d73ee84f8

import Mathlib
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S078
import Definitions.Def_OAIQ081S089
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Packing_incidence_mean_jointScore_le

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ConditionalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite conditional expectation by executable sequential search

An alphabet is given as an explicit nonempty list. With a duplicate-free list,
the averages below are uniform averages on words over that alphabet. No choice
oracle is used: `chooseMin` and `assign` are recursive finite algorithms.
-/

namespace SubexponentialSAT.ConditionalExpectation

open scoped BigOperators

variable {α : Type*}

theorem chooseMin_le (score : α → ℚ) (a : α) (tail : List α) :
    ∀ x ∈ a :: tail, score (chooseMin score a tail) ≤ score x := by
  induction tail generalizing a with
  | nil => simp [chooseMin]
  | cons b bs ih =>
      intro x hx
      simp only [chooseMin]
      split_ifs with h
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact h.trans (ih b x hx)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact le_of_lt (lt_of_not_ge h)
        · exact ih b x hx

theorem le_mean (alphabet : List α) (score : α → ℚ)
    (hne : alphabet ≠ []) (r : ℚ) (h : ∀ x ∈ alphabet, r ≤ score x) :
    r ≤ mean alphabet score := by
  have hsum : (alphabet.length : ℚ) * r ≤ (alphabet.map score).sum := by
    clear hne
    revert h
    induction alphabet with
    | nil => intro h; simp
    | cons a as ih =>
        intro h
        have ha : r ≤ score a := h a List.mem_cons_self
        have ht : ∀ x ∈ as, r ≤ score x := fun x hx => h x (List.mem_cons_of_mem a hx)
        have hi := ih ht
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
          List.sum_cons]
        nlinarith
  have hpos : (0 : ℚ) < alphabet.length := by
    exact_mod_cast List.length_pos_iff.mpr hne
  exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hsum)

theorem chooseMin_le_mean (score : α → ℚ) (a : α) (tail : List α) :
    score (chooseMin score a tail) ≤ mean (a :: tail) score :=
  le_mean (a :: tail) score (List.cons_ne_nil _ _)
    (score (chooseMin score a tail)) (chooseMin_le score a tail)

/-- Correctness of the search with a supplied exact evaluator. An efficient
local-probability evaluator may replace exhaustive enumeration once its two
identities below and its separate runtime bounds have been established. -/
theorem assignWithEvaluator_le (a : α) (tail : List α)
    (objective : List α → ℚ) (evaluate : ℕ → List α → ℚ)
    (hzero : ∀ fixed, evaluate 0 fixed = objective fixed)
    (hstep : ∀ n fixed, evaluate (n + 1) fixed =
      mean (a :: tail) (fun x => evaluate n (x :: fixed)))
    (n : ℕ) (fixed : List α) :
    objective (assignWithEvaluator a tail evaluate n fixed) ≤ evaluate n fixed := by
  induction n generalizing fixed with
  | zero => simp [assignWithEvaluator, hzero]
  | succ n ih =>
      rw [assignWithEvaluator, hstep]
      exact (ih _).trans (chooseMin_le_mean _ a tail)

end SubexponentialSAT.ConditionalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Variance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A finite dependency-graph variance bound

All expectations below are finite rational sums. The main theorem expands the
square of a centered count into a double sum of covariances. Nonneighbors have
zero covariance; at most `d + 1` entries in each row remain, each at most one.
-/

namespace SubexponentialSAT.Variance

open scoped BigOperators

variable {Ω V U : Type*}

section Mean

variable [Fintype Ω] (weight : Ω → ℚ)

theorem mean_const (hweight : ∑ ω, weight ω = 1) (a : ℚ) :
    mean weight (fun _ => a) = a := by
  rw [mean, ← Finset.sum_mul, hweight, one_mul]

theorem uniformWeight_sum [Nonempty Ω] : ∑ ω : Ω, uniformWeight ω = 1 := by
  have hcard : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [uniformWeight, div_eq_mul_inv, hcard]

end Mean

end SubexponentialSAT.Variance

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_TypeDistribution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform words induce uniform local types

The outcome space consists of all assignments of words to distinct factor,
head, and padding indices. Local read maps are injective. Read maps at
distinct coordinates sharing no factor have disjoint ranges. Finite product
counting then supplies the actual marginals and pair moments needed by
SubexponentialSAT.Variance; these probabilistic properties are conclusions, not hypotheses.
-/

namespace SubexponentialSAT.TypeDistribution

open scoped BigOperators
open SubexponentialSAT.SlotAssignment SubexponentialSAT.Variance

section EnumeratedExpectations

variable {I W A B : Type*}

theorem mean_prod_nested [Fintype A] [Fintype B] (F : A × B → ℚ) :
    mean uniformWeight F =
      mean uniformWeight (fun a : A => mean uniformWeight (fun b : B => F (a, b))) := by
  simp only [mean_uniformWeight, Fintype.sum_prod_type, Fintype.card_prod,
    Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, Finset.sum_mul, mul_assoc]

/-- Resampling any single word preserves the uniform mean. -/
theorem mean_resample [Fintype I] [DecidableEq I] [Fintype W] [Nonempty W]
    (i : I) (f : (I → W) → ℚ) :
    mean uniformWeight (fun ω : I → W =>
      mean uniformWeight (fun w : W => f (Function.update ω i w))) =
      mean uniformWeight f := by
  calc
    _ = mean uniformWeight (fun p : (I → W) × W =>
        f (Function.update p.1 i p.2)) := (mean_prod_nested _).symm
    _ = mean uniformWeight (fun p : (I → W) × W => f p.1) :=
      mean_equiv (resampleEquiv i) (fun p : (I → W) × W => f p.1)
    _ = _ := mean_prod_fst f

/-- Bridge from a recursively enumerated word expectation to the uniform
finite mean. Completeness of the coordinate list suffices: repeated resampling
of a coordinate also preserves the uniform distribution. The recursion
equations are explicit hypotheses so this applies to independently implemented
finite evaluators without introducing a second algorithm definition. -/
theorem recursive_word_mean_eq_uniform
    [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] [Nonempty W]
    (alphabet : List W) (hnodup : alphabet.Nodup) (hfull : ∀ w, w ∈ alphabet)
    (f : (I → W) → ℚ) (expect : List I → (I → W) → ℚ)
    (hzero : ∀ ω, expect [] ω = f ω)
    (hstep : ∀ i xs ω, expect (i :: xs) ω =
      SubexponentialSAT.ConditionalExpectation.mean alphabet
        (fun w => expect xs (Function.update ω i w)))
    (indices : List I) (hcover : ∀ i, i ∈ indices) (ω : I → W) :
    expect indices ω = mean uniformWeight f := by
  have hcongr : ∀ (xs : List I) (a b : I → W),
      (∀ i, i ∉ xs → a i = b i) → expect xs a = expect xs b := by
    intro xs
    induction xs with
    | nil =>
      intro a b h
      have hab : a = b := funext fun i => h i (by simp)
      rw [hab]
    | cons i xs ih =>
      intro a b h
      rw [hstep, hstep]
      apply congrArg (SubexponentialSAT.ConditionalExpectation.mean alphabet)
      funext w
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]
        exact h j (by simp [hji, hj])
  have havg (xs : List I) : mean uniformWeight (expect xs) = mean uniformWeight f := by
    induction xs with
    | nil =>
      apply congrArg (mean uniformWeight)
      funext a
      exact hzero a
    | cons i xs ih =>
      calc
        _ = mean uniformWeight (fun a : I → W =>
            mean uniformWeight (fun w : W => expect xs (Function.update a i w))) := by
          apply congrArg (mean uniformWeight)
          funext a
          rw [hstep, list_mean_eq_uniform alphabet hnodup hfull]
        _ = mean uniformWeight (expect xs) := mean_resample i (expect xs)
        _ = _ := ih
  have hc : expect indices = (fun _ : I → W => expect indices ω) := by
    funext a
    apply hcongr
    intro i hi
    exact (hi (hcover i)).elim
  calc
    expect indices ω = mean uniformWeight (fun _ : I → W => expect indices ω) :=
      (mean_const uniformWeight uniformWeight_sum _).symm
    _ = mean uniformWeight (expect indices) := congrArg (mean uniformWeight) hc.symm
    _ = _ := havg indices

end EnumeratedExpectations

section TypeCollisions

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq U]

theorem sum_fiberCount (τ : V → U) :
    (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ)) =
      (Fintype.card V : ℚ) := by
  have hc (u : U) :
      ((Finset.univ.filter fun v => τ v = u).card : ℚ) =
        ∑ v : V, if τ v = u then (1 : ℚ) else 0 := by simp
  simp_rw [hc]
  rw [Finset.sum_comm]
  simp

/-- Squared fiber counts count ordered pairs in the same fiber. -/
theorem sum_fiberCount_sq (τ : V → U) :
    (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2) =
      ∑ v : V, ∑ w : V, if τ v = τ w then (1 : ℚ) else 0 := by
  have hc (u : U) :
      ((Finset.univ.filter fun v => τ v = u).card : ℚ) =
        ∑ v : V, if τ v = u then (1 : ℚ) else 0 := by simp
  calc
    _ = ∑ u : U, ∑ v : V, ∑ w : V,
        (if τ v = u then (1 : ℚ) else 0) * (if τ w = u then (1 : ℚ) else 0) := by
      simp_rw [hc, pow_two, Finset.sum_mul, Finset.mul_sum]
    _ = ∑ v : V, ∑ w : V, ∑ u : U,
        (if τ v = u then (1 : ℚ) else 0) * (if τ w = u then (1 : ℚ) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      simp [ eq_comm]

/-- The global squared-deviation potential is a sum of local pair-collision
indicators minus a constant. This is the efficient-evaluation interface. -/
theorem squared_deviation_eq_collisions [Nonempty U] (τ : V → U) :
    (∑ u : U, (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
      (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) =
      (∑ v : V, ∑ w : V, if τ v = τ w then (1 : ℚ) else 0) -
        (Fintype.card V : ℚ) ^ 2 / (Fintype.card U : ℚ) := by
  have hN : (Fintype.card U : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexpand :
      (∑ u : U, (((Finset.univ.filter fun v => τ v = u).card : ℚ) -
        (Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) =
      (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2) -
        2 * ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) *
          (∑ u : U, ((Finset.univ.filter fun v => τ v = u).card : ℚ)) +
        (Fintype.card U : ℚ) *
          ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2 := by
    calc
      _ = ∑ u : U,
          (((Finset.univ.filter fun v => τ v = u).card : ℚ) ^ 2 -
          (2 * ((Fintype.card V : ℚ) / (Fintype.card U : ℚ))) *
            ((Finset.univ.filter fun v => τ v = u).card : ℚ) +
          ((Fintype.card V : ℚ) / (Fintype.card U : ℚ)) ^ 2) := by
        apply Finset.sum_congr rfl
        intro u _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hexpand, sum_fiberCount_sq, sum_fiberCount]
  field_simp
  ring

end TypeCollisions

end SubexponentialSAT.TypeDistribution

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_LocalExpectation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Conditional expectations of local objectives

A local term is evaluated only on the still-unassigned coordinates in its
support. The resulting evaluator is proved equal to exhaustive conditional
expectation. Instrumentation counts calls to local terms, separately from
arithmetic and data-structure costs.
-/

namespace SubexponentialSAT.LocalExpectation

open SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

theorem mean_add (alphabet : List W) (f g : W → ℚ) :
    mean alphabet (fun w => f w + g w) = mean alphabet f + mean alphabet g := by
  simp [mean, List.sum_map_add, add_div]

theorem mean_sub (alphabet : List W) (f g : W → ℚ) :
    mean alphabet (fun w => f w - g w) = mean alphabet f - mean alphabet g := by
  have h : (alphabet.map (fun w => f w - g w)).sum =
      (alphabet.map f).sum - (alphabet.map g).sum := by
    induction alphabet with
    | nil => simp
    | cons a as ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  simp only [mean, h, sub_div]

theorem wordExpectation_add (alphabet : List W) (f g : (I → W) → ℚ)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => f η + g η) remaining ω =
      wordExpectation alphabet f remaining ω + wordExpectation alphabet g remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      exact mean_add alphabet _ _

theorem wordExpectation_sub (alphabet : List W) (f g : (I → W) → ℚ)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => f η - g η) remaining ω =
      wordExpectation alphabet f remaining ω - wordExpectation alphabet g remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      exact mean_sub alphabet _ _

theorem wordExpectation_sum (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℚ) (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => (terms.map (fun j => f j η)).sum) remaining ω =
      (terms.map (fun j => wordExpectation alphabet (f j) remaining ω)).sum := by
  induction terms with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      induction remaining generalizing ω with
      | nil => rfl
      | cons i remaining ih => simp only [wordExpectation]; simp_rw [ih]; simp [mean]
  | cons j terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [wordExpectation_add, ih]

theorem localEvaluator_eq (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ)
    (remaining : List I) (ω : I → W) :
    localEvaluator alphabet terms support f offset remaining ω =
      wordExpectation alphabet (objective terms f offset) remaining ω := by
  unfold localEvaluator objective
  rw [wordExpectation_sub, wordExpectation_sum,
    wordExpectation_const alphabet hne]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  exact (wordExpectation_filter alphabet hne (support j) (f j) (hf j) remaining ω).symm

section Sequential

theorem sequentialEvaluator_zero (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (fixed : List W) :
    sequentialEvaluator alphabet terms support f offset default 0 fixed =
      objective terms f offset (decode default fixed) := by
  rw [sequentialEvaluator, localEvaluator_eq alphabet hne terms support f hf]
  rfl

theorem sequentialEvaluator_step (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (n : ℕ) (fixed : List W) :
    sequentialEvaluator alphabet terms support f offset default (n + 1) fixed =
      mean alphabet (fun w =>
        sequentialEvaluator alphabet terms support f offset default n (w :: fixed)) := by
  simp only [sequentialEvaluator]
  simp_rw [localEvaluator_eq alphabet hne terms support f hf]
  simp only [List.range'_succ, wordExpectation, decode, List.length_cons]

theorem localAssign_le_initial (a : W) (tail : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W) (n : ℕ) :
    objective terms f offset (decode default (localAssign a tail terms support f offset default n)) ≤
      sequentialEvaluator (a :: tail) terms support f offset default n [] := by
  exact assignWithEvaluator_le a tail
    (fun xs => objective terms f offset (decode default xs))
    (sequentialEvaluator (a :: tail) terms support f offset default)
    (sequentialEvaluator_zero _ (List.cons_ne_nil _ _) terms support f hf offset default)
    (sequentialEvaluator_step _ (List.cons_ne_nil _ _) terms support f hf offset default) n []

end Sequential

section Reindex

omit [DecidableEq I] in
theorem reindexTerm_dependsOn (code : I → ℕ) (support : Finset I)
    (f : (I → W) → ℚ) (hf : DependsOn support f) :
    DependsOn (support.image code) (reindexTerm code f) := by
  intro ξ ξ' h
  apply hf
  intro i hi
  exact h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem wordExpectation_reindex (alphabet : List W) (code : I → ℕ)
    (hcode : Function.Injective code) (f : (I → W) → ℚ)
    (remaining : List I) (ξ : ℕ → W) :
    wordExpectation alphabet (reindexTerm code f) (remaining.map code) ξ =
      wordExpectation alphabet f remaining (fun i => ξ (code i)) := by
  induction remaining generalizing ξ with
  | nil => rfl
  | cons i remaining ih =>
      simp only [List.map_cons, wordExpectation]
      apply congrArg (mean alphabet)
      funext w
      rw [ih]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j; simp
      · have hc : code j ≠ code i := fun h => hji (hcode h)
        simp [Function.update_of_ne hji, Function.update_of_ne hc]

/-- Explicit `idxOf` numbering preserves the initial conditional mean. -/
theorem initialEvaluator_reindex_eq (alphabet : List W) (ha : alphabet ≠ [])
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (indices : List I) (hn : indices.Nodup) (hc : ∀ i, i ∈ indices) :
    sequentialEvaluator alphabet terms
      (fun j => (support j).image (fun i => indexCode indices i))
      (fun j => reindexTerm (fun i => indexCode indices i) (f j)) offset default
      indices.length [] =
    wordExpectation alphabet (objective terms f offset) indices (fun _ => default) := by
  unfold sequentialEvaluator
  rw [localEvaluator_eq alphabet ha _ _ _
    (fun j => reindexTerm_dependsOn _ _ _ (hf j))]
  change wordExpectation alphabet
    (reindexTerm (fun i => indexCode indices i) (objective terms f offset))
      (List.range' 0 indices.length) (fun _ => default) = _
  rw [← List.range_eq_range', ← map_idxOf_eq_range indices hn,
    wordExpectation_reindex alphabet _ (idxOf_injective indices hc)]

/-- Full explicit enumerations turn the initial local evaluator into the
ordinary uniform mean on all independent word assignments. -/
theorem initialEvaluator_reindex_uniform [Fintype I] [Fintype W]
    [DecidableEq W] [Nonempty W]
    (alphabet : List W) (ha : alphabet ≠ []) (haNodup : alphabet.Nodup)
    (haFull : ∀ w, w ∈ alphabet)
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (indices : List I) (hn : indices.Nodup) (hc : ∀ i, i ∈ indices) :
    sequentialEvaluator alphabet terms
      (fun j => (support j).image (fun i => indexCode indices i))
      (fun j => reindexTerm (fun i => indexCode indices i) (f j)) offset default
      indices.length [] =
    SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight (objective terms f offset) := by
  rw [initialEvaluator_reindex_eq alphabet ha terms support f hf offset default indices hn hc]
  exact SubexponentialSAT.TypeDistribution.recursive_word_mean_eq_uniform alphabet haNodup haFull
    (objective terms f offset) (wordExpectation alphabet (objective terms f offset))
    (fun _ => rfl) (fun _ _ _ => rfl) indices hc _

end Reindex

end SubexponentialSAT.LocalExpectation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingVariance
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact collision-energy bounds used in correlated incidence packing. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance

noncomputable section

variable {Ω I U : Type*} [Fintype Ω] [Fintype I] [Fintype U]
  [DecidableEq I] [DecidableEq U] [Nonempty Ω] [Nonempty U]

omit [DecidableEq I] [Nonempty U] in
theorem energy_nonneg (label : I → U) : 0 ≤ energy label := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq I] in
theorem energy_eq_collisions (label : I → U) :
    energy label = (∑ i, ∑ j, if label i = label j then (1 : ℚ) else 0) -
      (Fintype.card I : ℚ)^2 / (Fintype.card U : ℚ) := by
  exact SubexponentialSAT.TypeDistribution.squared_deviation_eq_collisions label

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual shared-head/shared-factor words on an arbitrary finite incidence set. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes

noncomputable section

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

variable [NeZero r]

omit [Fintype E] [DecidableEq E] in
omit [DecidableEq V] [NeZero r] in
theorem headEnergy_nonneg (ω : WordAssignment V E r Q) : 0 ≤ headEnergy ω :=
  Finset.sum_nonneg fun _ _ => energy_nonneg _

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Simultaneous type packing and original-variable head balance. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes
noncomputable section

section Joint
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

omit [Fintype Ω] [Nonempty Ω] in
theorem jointScore_controls (X Y : Ω → ℚ) {x y : ℚ} (hx : 0 < x) (hy : 0 < y)
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) (ω : Ω)
    (h : jointScore X Y x y ω ≤ x^2*y^2) : X ω ≤ x^2 ∧ Y ω ≤ y^2 := by
  have hx2 : 0 < x^2 := sq_pos_of_pos hx
  have hy2 : 0 < y^2 := sq_pos_of_pos hy
  have h0X := mul_nonneg (le_of_lt hy2) (hX ω)
  have h0Y := mul_nonneg (le_of_lt hx2) (hY ω)
  dsimp [jointScore] at h
  constructor
  · exact le_of_mul_le_mul_left (by nlinarith) hy2
  · exact le_of_mul_le_mul_left (by nlinarith) hx2

end Joint

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingAlgorithm
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A deterministic conditional-expectation algorithm with at most four word reads per term. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Algorithm
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem scoreTerm_dependsOn (x y : ℚ) (z : ScoreTerm I V Q) :
    DependsOn (scoreSupport ivar factor z) (scoreTerm (r := r) ivar factor x y z) := by
  intro ω ω' h
  cases z with
  | inl p =>
    rcases p with ⟨i,j⟩
    have hi : incidenceType ivar factor ω i = incidenceType ivar factor ω' i := by
      apply UniversalType.ext
      · exact h _ (by simp [scoreSupport])
      · funext s
        exact h _ (by simp [scoreSupport])
    have hj : incidenceType ivar factor ω j = incidenceType ivar factor ω' j := by
      apply UniversalType.ext
      · exact h _ (by simp [scoreSupport])
      · funext s
        exact h _ (by simp [scoreSupport])
    simp only [scoreTerm, hi, hj]
  | inr p =>
    rcases p with ⟨t,v,w⟩
    have hv := h (Sum.inl v) (by simp [scoreSupport])
    have hw := h (Sum.inl w) (by simp [scoreSupport])
    simp only [scoreTerm, hv, hw]

variable [NeZero r]

private theorem sum_list_eq {T : Type*} [Fintype T] [DecidableEq T]
    (xs : List T) (hn : xs.Nodup) (hc : ∀ t, t ∈ xs) (f : T → ℚ) :
    (xs.map f).sum = ∑ t, f t := by
  rw [← List.sum_toFinset f hn]
  have hs : xs.toFinset = Finset.univ := by ext t; simp [hc t]
  rw [hs]

omit [Fintype E] [DecidableEq E] in
theorem objective_score_eq (terms : List (ScoreTerm I V Q))
    (hn : terms.Nodup) (hc : ∀ z, z ∈ terms) (x y : ℚ)
    (ω : WordAssignment V E r Q) :
    objective terms (scoreTerm ivar factor x y) (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) ω =
      jointScore (fun η => energy (incidenceType ivar factor η)) headEnergy x y ω := by
  unfold objective
  rw [sum_list_eq terms hn hc, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, scoreTerm]
  unfold jointScore headEnergy scoreOffset
  dsimp only
  rw [energy_eq_collisions]
  simp_rw [energy_eq_collisions]
  simp only [Fintype.card_fin, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  ring

omit [NeZero r] in
omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedScoreTerm_dependsOn (indices : List (V ⊕ E)) (x y : ℚ)
    (z : ScoreTerm I V Q) :
    DependsOn (numberedScoreSupport ivar factor indices z)
      (numberedScoreTerm (r := r) ivar factor indices x y z) :=
  reindexTerm_dependsOn _ _ _ (scoreTerm_dependsOn ivar factor x y z)

theorem computedWords_score_le_mean (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ w, w ∈ a::tail)
    (terms : List (ScoreTerm I V Q)) (htN : terms.Nodup) (htC : ∀ z, z ∈ terms)
    (indices : List (V ⊕ E)) (hiN : indices.Nodup) (hiC : ∀ i, i ∈ indices)
    (x y : ℚ) :
    jointScore (fun η => energy (incidenceType ivar factor η)) headEnergy x y
      (computedWords ivar factor a tail terms indices x y) ≤
    SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight
      (jointScore (fun η : WordAssignment V E r Q => energy (incidenceType ivar factor η))
        headEnergy x y) := by
  have h := localAssign_le_initial a tail terms (numberedScoreSupport ivar factor indices)
    (numberedScoreTerm ivar factor indices x y)
    (numberedScoreTerm_dependsOn ivar factor indices x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a indices.length
  have heq := initialEvaluator_reindex_uniform (a::tail) (List.cons_ne_nil _ _) haN haC
    terms (scoreSupport ivar factor) (scoreTerm ivar factor x y)
    (scoreTerm_dependsOn ivar factor x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a indices hiN hiC
  have ho : objective terms (scoreTerm (r := r) ivar factor x y)
      (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) =
      jointScore (fun η => energy (incidenceType ivar factor η)) headEnergy x y := by
    funext ω
    exact objective_score_eq ivar factor terms htN htC x y ω
  rw [ho] at heq
  rw [← heq]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  exact (objective_score_eq ivar factor terms htN htC x y _).symm
  rfl

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingPrefix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Heads-first numbering and the actual reverse-list assignment prefix. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Indices
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
theorem headsFirst_nodup (vertices : List V) (factors : List E)
    (hv : vertices.Nodup) (he : factors.Nodup) :
    (headsFirstIndices vertices factors).Nodup := by
  simp only [headsFirstIndices, List.nodup_append]
  refine ⟨hv.map Sum.inl_injective, he.map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
  simp at hab
end Indices

end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingTheorem
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end correlated incidence packing with balanced original heads. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
noncomputable section

variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

/-- The searched words meet both quantitative energy budgets. -/
theorem computedWords_energies (a₀ : Word r Q) (tail : List (Word r Q))
    (haN : (a₀::tail).Nodup) (haC : ∀ w, w ∈ a₀::tail)
    (terms : List (ScoreTerm I V Q)) (htN : terms.Nodup) (htC : ∀ z, z ∈ terms)
    (indices : List (V ⊕ E)) (hiN : indices.Nodup) (hiC : ∀ i, i ∈ indices)
    (ε : ℚ) (hε : 0 < ε) (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
    (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
    (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
      ε^2*(Fintype.card I : ℚ))
    (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
    let x := ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ)
    let y := (Fintype.card V : ℚ)/(2*(r : ℚ))
    let ω := computedWords ivar factor a₀ tail terms indices x y
    energy (incidenceType ivar factor ω) ≤ x^2 ∧ headEnergy ω ≤ y^2 := by
  dsimp only
  have hI : (0 : ℚ) < Fintype.card I := by exact_mod_cast hM
  have hV : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  have hN : (0 : ℚ) < Fintype.card (UniversalType r Q 1) := by
    exact_mod_cast Fintype.card_pos
  have hr : (0 : ℚ) < r := by exact_mod_cast Nat.pos_of_neZero r
  apply jointScore_controls _ _ (by positivity) (by positivity)
    (fun ω => energy_nonneg (incidenceType ivar factor ω)) headEnergy_nonneg
  exact (computedWords_score_le_mean ivar factor a₀ tail haN haC terms htN htC
    indices hiN hiC _ _).trans
      (incidence_mean_jointScore_le ivar factor ε hε B a hB ha hM hn hlarge hhead)

end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedHeadsScope
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldE _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native scope selector has precisely the rational weights required by
the correlated-packing proof. All lists here are the actual producer lists. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LayoutProducedHeads
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes PackingProgram
open PackingProgram.Assembly

theorem scope_terms_complete (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (Q : ℕ) : ∀ z,z ∈ Scope.terms scopes n mask Q := by
  intro z
  cases z with
  | inl p =>
    rcases p with ⟨i,j⟩
    simp [Scope.terms,Scope.pairs,PackingIncidenceInput.Finished.incidenceList]
  | inr p => rcases p with ⟨t,v,w⟩; simp [Scope.terms,PackingHeadIncremental.headTerms]

theorem scope_terms_nodup (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool)
    (Q : ℕ) : (Scope.terms scopes n mask Q).Nodup := by
  let vertices := List.finRange n
  let heads := (List.finRange Q).product (vertices.product vertices)
  have he : PackingHeadIncremental.headTerms
      (I := PackingIncidenceInput.Semantics.Incidences scopes mask) (Q := Q) vertices =
      heads.map (fun z => Sum.inr (z.1,z.2.1,z.2.2)) := by
    simp [PackingHeadIncremental.headTerms,heads,List.product,List.map_flatMap,
      List.map_map,Function.comp_def]
  have hh : heads.Nodup := (List.nodup_finRange Q).product
    ((List.nodup_finRange n).product (List.nodup_finRange n))
  have hi : Function.Injective (fun z : Fin Q × Fin n × Fin n =>
      (Sum.inr (z.1,z.2.1,z.2.2) : Packing.ScoreTerm
        (PackingIncidenceInput.Semantics.Incidences scopes mask) (Fin n) Q)) := by
    intro z w h; simpa using h
  unfold Scope.terms
  change ((Scope.pairs scopes mask).map Sum.inl ++
    PackingHeadIncremental.headTerms vertices).Nodup
  rw [he,List.nodup_append]
  refine ⟨?_,hh.map hi,?_⟩
  · exact ((List.nodup_finRange _).product (List.nodup_finRange _)).map Sum.inl_injective
  · intro x hx y hy hxy
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hy
    exact Sum.inl_ne_inr hxy

theorem problem_computed_energies_oai (p : PackingCallerProgram.Problem)
    (a : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (haN : (a::tail).Nodup) (haC : ∀ z,z∈a::tail) (B b : ℕ)
    (hB : ∀ v,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le i=v).card ≤ B)
    (hb : ∀ e,(Finset.univ.filter fun i =>
      PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le i=e).card ≤ b)
    (hM : 0 < p.incidences) (hn : 0 < p.n)
    (hlarge : 4*(B+b)*(p.r^(2*p.Q))^2*p.s^2 ≤ p.incidences)
    (hhead : 16*p.Q*p.r^2 ≤ p.n) :
    Packing.energy (Packing.incidenceType
      (PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le)
      (PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le)
      (problemAssignment p a tail)) ≤ (problemX p)^2 ∧
    Packing.headEnergy (problemAssignment p a tail) ≤ ((p.n:ℚ)/(2*(p.r:ℚ)))^2 := by
  let : NeZero p.r := ⟨Nat.ne_of_gt p.hr⟩
  let own := PackingIncidenceInput.Semantics.owner p.scopes p.n p.mask p.mask_le
  let fac := PackingIncidenceInput.Semantics.factor p.scopes p.n p.mask p.mask_le
  let ts := Scope.terms p.scopes p.n p.mask p.Q
  let ids := PackingIncidenceInput.Semantics.seedIndices p.n p.factors
  let eps : ℚ := 1/p.s
  have hs : (0:ℚ) < p.s := by exact_mod_cast p.hs
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hbig : 4*((B+b:ℕ):ℚ)*(Fintype.card (UniversalType p.r p.Q 1):ℚ)^2 ≤
      eps^2*(p.incidences:ℚ) := by
    have hc : Fintype.card (UniversalType p.r p.Q 1)=p.r^(2*p.Q) := by
      simp [Nat.mul_comm]
    have hh : (4*((B+b:ℕ):ℚ)*(Fintype.card (UniversalType p.r p.Q 1):ℚ)^2)*
        (p.s:ℚ)^2 ≤ p.incidences := by rw [hc]; exact_mod_cast hlarge
    calc
      _ ≤ (p.incidences:ℚ)/(p.s:ℚ)^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr hh
      _ = _ := by dsimp [eps]; ring
  have hg := Packing.computedWords_energies own fac a tail haN haC ts
    (scope_terms_nodup p.scopes p.n p.mask p.Q)
    (scope_terms_complete p.scopes p.n p.mask p.Q) ids
    (Packing.headsFirst_nodup _ _ (List.nodup_finRange _) (List.nodup_finRange _))
    (PackingIncidenceInput.Semantics.seedIndices_complete _ _) eps heps B b hB hb
    (by simpa only [Fintype.card_fin, PackingCallerProgram.Problem.incidences] using hM)
    (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin, PackingCallerProgram.Problem.incidences] using hbig)
    (by norm_cast; simpa only [Fintype.card_fin] using hhead)
  simpa only [problemAssignment,problemX,ids,eps,own,fac,ts,Fintype.card_fin,
    PackingCallerProgram.Problem.incidences] using hg

end SubexponentialSAT.SqrtLog.LayoutProducedHeads

end
end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies_oai
