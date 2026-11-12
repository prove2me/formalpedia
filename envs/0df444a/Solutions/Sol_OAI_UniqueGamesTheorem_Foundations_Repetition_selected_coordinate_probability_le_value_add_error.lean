-- Prove2me | solution 1 for OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:14:03.132207+00:00
-- url     : https://prove2.me/submissions/aeafe9b2-d87a-4ac9-80b3-02380ccc4b0e

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P011

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Basic
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite prerequisites for Holenstein's consistent sampling argument (Lemma 5.2).

`firstAccepted` is an actual bounded rejection sampler on a shared finite list
of proposals. `first_union_common` proves its synchronization property.
The remaining theorems establish the exact overlap/union mass formulas and the
agreement lower bound used to analyze a first accepted shared proposal.

No infinite random process or locally computable embedding is asserted here.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

/-- If the first proposal accepted by either sampler is accepted by both,
the two samplers return exactly that same proposal. -/
theorem first_union_common {σ : Type*} (left right : σ → Bool)
    (proposals : List σ) (proposal : σ)
    (hfirst : firstAccepted (fun s => left s || right s) proposals = some proposal)
    (hleft : left proposal = true) (hright : right proposal = true) :
    firstAccepted left proposals = some proposal ∧
      firstAccepted right proposals = some proposal := by
  induction proposals with
  | nil => simp [firstAccepted] at hfirst
  | cons head tail ih =>
      by_cases hl : left head = true
      · have heq : head = proposal := by
          simpa [firstAccepted, hl] using hfirst
        subst head
        simp [firstAccepted, hleft, hright]
      · by_cases hr : right head = true
        · have heq : head = proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          subst head
          exact False.elim (hl hleft)
        · have htail : firstAccepted (fun s => left s || right s) tail = some proposal := by
            simpa [firstAccepted, hl, hr] using hfirst
          simpa [firstAccepted, hl, hr] using ih htail

noncomputable section FiniteWeights

variable {α : Type*} [Fintype α]

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

private theorem max_abs_identity (x y : ℝ) : 2 * max x y - |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- The union of two probability masses is exactly one plus their TV. -/
theorem unionMass_eq (p q : α → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    unionMass p q = 1 + totalVariation p q := by
  have h := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun a _ => max_abs_identity (p a) (q a))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq] at h
  unfold unionMass totalVariation
  linarith

end FiniteWeights

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_FiniteTrialsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite probability mass of a bounded rejection process.

Each trial independently draws from a finite mass function `w`. Its first
accepted proposal is represented by `some proposal`; exhaustion is `none`.
The recursive definition exposes the one-step probability transition. We prove
normalization, nonnegativity, the exact survival probability, and an exact
agreement-event formula with the finite-truncation error.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

theorem eventMass_nonneg (w : σ → ℝ) (event : σ → Bool) (hw : ∀ s, 0 ≤ w s) :
    0 ≤ eventMass w event := by
  apply Finset.sum_nonneg
  intro s _
  split <;> simp_all

theorem eventMass_complement (w : σ → ℝ) (event : σ → Bool)
    (hw : ∑ s, w s = 1) :
    eventMass w event + eventMass w (fun s => !(event s)) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  calc
    ∑ s, ((if event s then w s else 0) + (if !event s then w s else 0)) = ∑ s, w s := by
      apply Finset.sum_congr rfl
      intro s _
      cases event s <;> simp
    _ = 1 := hw

theorem geometricMass_identity (r : ℝ) (n : Nat) :
    (1 - r) * geometricMass r n = 1 - r ^ n := by
  induction n with
  | zero => simp [geometricMass]
  | succ n ih =>
      simp only [geometricMass, pow_succ]
      calc
        (1 - r) * (1 + r * geometricMass r n) =
            (1 - r) + r * ((1 - r) * geometricMass r n) := by ring
        _ = 1 - r ^ n * r := by rw [ih]; ring

theorem firstHitWeight_some (w : σ → ℝ) (accept : σ → Bool) (n : Nat) (s : σ) :
    firstHitWeight w accept n (some s) =
      (if accept s then w s else 0) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  induction n with
  | zero => simp [firstHitWeight, geometricMass]
  | succ n ih =>
      rw [firstHitWeight, geometricMass, ih]
      ring

theorem goodFirstMass_eq (w : σ → ℝ) (accept good : σ → Bool) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) *
        geometricMass (eventMass w (fun s => !(accept s))) n := by
  unfold goodFirstMass eventMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [firstHitWeight_some]
  cases ha : accept s <;> cases hg : good s <;> simp [ha, hg, eventMass]

/-- Exact finite geometric law: the first accepted proposal lies in the good
part with probability (good accepted mass / total accepted mass) times the
probability of seeing any accepted proposal within the trial bound. -/
theorem goodFirstMass_exact (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (ha : eventMass w accept ≠ 0) (n : Nat) :
    goodFirstMass w accept good n =
      eventMass w (fun s => accept s && good s) / eventMass w accept *
        (1 - eventMass w (fun s => !(accept s)) ^ n) := by
  rw [goodFirstMass_eq]
  have hc := eventMass_complement w accept hw
  have hg := geometricMass_identity (eventMass w (fun s => !(accept s))) n
  have hgeom : eventMass w accept *
      geometricMass (eventMass w (fun s => !(accept s))) n =
      1 - eventMass w (fun s => !(accept s)) ^ n := by
    have heq : eventMass w accept = 1 - eventMass w (fun s => !(accept s)) := by linarith
    rw [heq, hg]
  rw [← hgeom]
  field_simp

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-! A finite exact replacement for uniform real thresholds. A list of real
thresholds subdivides [0,1]. Each resulting interval is an atom with weight its
length. Every inserted threshold has exactly its stated acceptance mass. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

theorem split_cdf (I : ThresholdInterval) (t r : ℝ) :
    intervalCDF r (splitLeft I t) + intervalCDF r (splitRight I t) = intervalCDF r I := by
  unfold intervalCDF splitLeft splitRight
  ring

theorem accepted_interval_mass (I : ThresholdInterval) (r : ℝ) (hc : cutAt r I) :
    (if I.lo < r then I.hi - I.lo else 0) = intervalCDF r I := by
  by_cases hl : I.lo < r
  · have hu : I.hi ≤ r := hc.resolve_right (not_le_of_gt hl)
    simp [hl, intervalCDF, min_eq_right hu, min_eq_right (le_of_lt hl)]
  · have hr : r ≤ I.lo := le_of_not_gt hl
    simp [hl, intervalCDF, min_eq_left hr, min_eq_left (hr.trans I.valid)]

theorem splitLeft_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitLeft I t) := by
  by_cases h : I.lo ≤ t
  · exact Or.inl (max_le h (min_le_left _ _))
  · exact Or.inr (le_of_lt (lt_of_not_ge h))

theorem splitRight_cut (I : ThresholdInterval) (t : ℝ) : cutAt t (splitRight I t) := by
  by_cases h : t ≤ I.hi
  · right
    change t ≤ max I.lo (min t I.hi)
    rw [min_eq_left h]
    exact le_max_right _ _
  · exact Or.inl (le_of_lt (lt_of_not_ge h))

theorem splitLeft_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitLeft I t) := by
  rcases h with h | h
  · exact Or.inl ((max_le I.valid (min_le_right _ _)).trans h)
  · exact Or.inr h

theorem splitRight_preserves_cut (I : ThresholdInterval) (t r : ℝ) (h : cutAt r I) :
    cutAt r (splitRight I t) := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (le_max_left _ _))

theorem partition_cdf (thresholds : List ℝ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) = r := by
  have h := partition_sum (intervalCDF r) (fun t I => split_cdf I t r) thresholds
  simpa [intervalCDF, unitThresholdInterval, min_eq_left h1, min_eq_right h0] using h

theorem splitAll_new_cuts (intervals : List ThresholdInterval) (t : ℝ) :
    ∀ I ∈ splitAll t intervals, cutAt t I := by
  induction intervals with
  | nil => intro I h; simp [splitAll] at h
  | cons J rest ih =>
      intro I h
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_cut J t
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_cut J t
        · exact ih I h

theorem splitAll_preserves_cuts (intervals : List ThresholdInterval) (t r : ℝ) :
    (∀ I ∈ intervals, cutAt r I) → ∀ I ∈ splitAll t intervals, cutAt r I := by
  induction intervals with
  | nil => intro _ I h; simp [splitAll] at h
  | cons J rest ih =>
      intro hc I h
      have hJ : cutAt r J := hc J (by simp)
      have hrest : ∀ K ∈ rest, cutAt r K := fun K hK => hc K (by simp [hK])
      rcases List.mem_cons.mp h with h | h
      · subst I; exact splitLeft_preserves_cut J t r hJ
      · rcases List.mem_cons.mp h with h | h
        · subst I; exact splitRight_preserves_cut J t r hJ
        · exact ih hrest I h

theorem partition_cuts (thresholds : List ℝ) (r : ℝ) :
    r ∈ thresholds → ∀ I ∈ thresholdPartition thresholds, cutAt r I := by
  induction thresholds with
  | nil => intro hr; simp at hr
  | cons t rest ih =>
      intro hr
      rcases List.mem_cons.mp hr with h | h
      · subst r; exact splitAll_new_cuts (thresholdPartition rest) t
      · exact splitAll_preserves_cuts (thresholdPartition rest) t r (ih h)

theorem sumOnIntervals_congr (f g : ThresholdInterval → ℝ) (intervals : List ThresholdInterval) :
    (∀ I ∈ intervals, f I = g I) → sumOnIntervals f intervals = sumOnIntervals g intervals := by
  induction intervals with
  | nil => intro _; rfl
  | cons J rest ih =>
      intro h
      have hJ := h J (by simp)
      have hr : ∀ I ∈ rest, f I = g I := fun I hI => h I (by simp [hI])
      simp only [sumOnIntervals, hJ, ih hr]

theorem partition_acceptance_mass (thresholds : List ℝ) (r : ℝ)
    (hr : r ∈ thresholds) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    sumOnIntervals (fun I => if I.lo < r then I.hi - I.lo else 0)
      (thresholdPartition thresholds) = r := by
  calc
    _ = sumOnIntervals (intervalCDF r) (thresholdPartition thresholds) :=
      sumOnIntervals_congr _ _ _ (fun I hI =>
        accepted_interval_mass I r (partition_cuts thresholds r hr I hI))
    _ = r := partition_cdf thresholds r h0 h1

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-!
Connect the rejection sampler's executable list recursion to exact finite
probabilities. `traceAverage` is a finite nested sum over independent proposals;
it introduces no assumed probability law. The main theorem computes the actual
mass of each output of `firstAccepted` under those nested sums.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ : Type*} [Fintype σ]

theorem traceAverage_const (w : σ → ℝ) (hw : ∑ s, w s = 1) (n : Nat) (c : ℝ) :
    traceAverage w n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traceAverage, ih, ← Finset.sum_mul, hw]

theorem traceAverage_mono (w : σ → ℝ) (hw : ∀ s, 0 ≤ w s) (n : Nat)
    (f g : List σ → ℝ) (hfg : ∀ xs, f xs ≤ g xs) :
    traceAverage w n f ≤ traceAverage w n g := by
  induction n generalizing f g with
  | zero => exact hfg []
  | succ n ih =>
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (ih (fun tail => f (s :: tail)) (fun tail => g (s :: tail))
          (fun tail => hfg (s :: tail))) (hw s)

theorem traceAverage_sum {ι : Type*} [Fintype ι] (w : σ → ℝ) (n : Nat)
    (f : ι → List σ → ℝ) :
    traceAverage w n (fun xs => ∑ i, f i xs) = ∑ i, traceAverage w n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [traceAverage]
      simp_rw [ih, Finset.mul_sum]
      exact Finset.sum_comm

variable [DecidableEq σ]

/-- The recursively constructed first-hit distribution is the actual law
of the finite shared-list rejection sampler. -/
theorem firstAccepted_law (w : σ → ℝ) (accept : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) (output : Option σ) :
    traceAverage w n (fun proposals =>
      if firstAccepted accept proposals = output then 1 else 0) =
      firstHitWeight w accept n output := by
  classical
  induction n generalizing output with
  | zero => cases output <;> simp [traceAverage, firstAccepted, firstHitWeight]
  | succ n ih =>
      have hstep : traceAverage w (n + 1) (fun proposals =>
          if firstAccepted accept proposals = output then 1 else 0) =
          ∑ s, w s * (if accept s then (if some s = output then 1 else 0)
            else firstHitWeight w accept n output) := by
        unfold traceAverage
        apply Finset.sum_congr rfl
        intro s _
        congr 1
        by_cases hs : accept s = true
        · simp [firstAccepted, hs, traceAverage_const w hw]
        · simpa [firstAccepted, hs] using ih output
      rw [hstep]
      cases output with
      | none =>
          simp only [Option.some_ne_none, ite_false, if_false, firstHitWeight]
          rw [eventMass, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          cases accept s <;> simp
      | some t =>
          simp only [Option.some.injEq, firstHitWeight]
          calc
            ∑ s, w s * (if accept s then (if s = t then 1 else 0)
                else firstHitWeight w accept n (some t)) =
              ∑ s, ((if s = t then (if accept s then w s else 0) else 0) +
                (if !(accept s) then w s else 0) * firstHitWeight w accept n (some t)) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  by_cases he : s = t
                  · subst s
                    by_cases hs : accept t = true <;> simp [hs]
                  · by_cases hs : accept s = true <;> simp [hs, he]
            _ = (if accept t then w t else 0) +
                eventMass w (fun s => !(accept s)) * firstHitWeight w accept n (some t) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                  simp [eventMass]

theorem goodFirstIndicator_expansion (accept good : σ → Bool) (proposals : List σ) :
    goodFirstIndicator accept good proposals =
      ∑ s, if good s then (if firstAccepted accept proposals = some s then 1 else 0) else 0 := by
  classical
  cases h : firstAccepted accept proposals with
  | none => simp [goodFirstIndicator, h]
  | some t =>
      simp only [goodFirstIndicator, h, Option.some.injEq]
      calc
        (if good t then (1 : ℝ) else 0) =
            ∑ s, if t = s then (if good s then (1 : ℝ) else 0) else 0 := by simp
        _ = ∑ s, if good s then (if t = s then (1 : ℝ) else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s _
          by_cases hg : good s = true <;> by_cases ht : t = s <;> simp [hg, ht]

/-- Exact good-event probability of the actual bounded sampler. -/
theorem goodFirstIndicator_law (w : σ → ℝ) (accept good : σ → Bool)
    (hw : ∑ s, w s = 1) (n : Nat) :
    traceAverage w n (goodFirstIndicator accept good) = goodFirstMass w accept good n := by
  classical
  change traceAverage w n (fun xs => goodFirstIndicator accept good xs) = _
  simp_rw [goodFirstIndicator_expansion]
  rw [traceAverage_sum]
  unfold goodFirstMass
  apply Finset.sum_congr rfl
  intro s _
  by_cases hg : good s = true
  · simpa [hg] using firstAccepted_law w accept hw n (some s)
  · simp [hg, traceAverage_const w hw]

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

/-- An acceptance implication under an exact question-law pushforward gives an
actual success-probability comparison for every pair of local strategies. -/
theorem success_le_of_localSimulation {R₁ R₂ B₁ B₂ : Type*}
    [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (questionMap₁ : Q₁ → R₁) (questionMap₂ : Q₂ → R₂)
    (answerMap₁ : Q₁ → B₁ → A₁) (answerMap₂ : Q₂ → B₂ → A₂)
    (questionLaw : H.questions =
      G.questions.pushforward (fun q => (questionMap₁ q.1, questionMap₂ q.2)))
    (acceptance : ∀ x y a b,
      H.accepts (questionMap₁ x) (questionMap₂ y) a b = true →
      G.accepts x y (answerMap₁ x a) (answerMap₂ y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤
      G.success (simulatedStrategy questionMap₁ questionMap₂ answerMap₁ answerMap₂ strategy) := by
  unfold success
  rw [questionLaw, FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro questions h
  exact acceptance questions.1 questions.2 _ _ h

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

theorem success_le_value (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) : G.success strategy ≤ G.value := by
  classical
  exact Finset.le_sup' G.success (Finset.mem_univ strategy)

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

theorem table_eval_pushforward [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (q₀ : Q) :
    (table responses).pushforward (fun answers => answers q₀) = responses q₀ := by
  classical
  apply eq_of_weight_eq
  intro a
  calc
    _ = (table responses).expectation
        (fun answers => if answers q₀ = a then 1 else 0) := by
      simp [pushforward, expectation, mul_ite]
    _ = (responses q₀).expectation (fun b => if b = a then 1 else 0) :=
      expectation_table_eval responses q₀ (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [expectation, mul_ite]

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

/-- Applying separate maps to independent samples preserves their independence. -/
theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

/-- A full response table of nonzero weight uses a supported answer in every row. -/
theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

/-- Repairing table entries only off each row's support leaves its exact law intact. -/
theorem table_repair_pushforward
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (repair : Q → A → A)
    (hrepair : ∀ q a, (responses q).weight a ≠ 0 → repair q a = a) (q : Q) :
    (table responses).pushforward (fun answers => repair q (answers q)) =
      responses q := by
  calc
    _ = (table responses).pushforward (fun answers => answers q) := by
      apply pushforward_eq_of_agree_on_support
      intro answers h
      exact hrepair q (answers q) (table_row_weight_ne_zero responses answers h q)
    _ = responses q := table_eval_pushforward responses q

end FiniteDistribution

namespace KernelSampling

/-- The two reads have exactly the product of the requested conditional laws. -/
theorem read_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed => (readLeft seed x, readRight seed y)) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => answers x) (fun answers => answers y),
    FiniteDistribution.table_eval_pushforward, FiniteDistribution.table_eval_pushforward]

/-- Separate supported repairs retain the exact joint product law. -/
theorem repaired_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (repairLeft : Q₁ → A → A) (repairRight : Q₂ → B → B)
    (hleft : ∀ x a, (left x).weight a ≠ 0 → repairLeft x a = a)
    (hright : ∀ y b, (right y).weight b ≠ 0 → repairRight y b = b)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed =>
      (repairLeft x (readLeft seed x), repairRight y (readRight seed y))) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => repairLeft x (answers x)) (fun answers => repairRight y (answers y)),
    FiniteDistribution.table_repair_pushforward left repairLeft hleft,
    FiniteDistribution.table_repair_pushforward right repairRight hright]

section Completion

variable {I A B S : Type*} [DecidableEq I]

private theorem update_eq_of_coordinate (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

/-- Exact conditional completion from a finite weighted shared seed. The reads
always restore the specified coordinates, including on seeds of weight zero;
the support hypotheses ensure that this repair preserves the requested laws. -/
theorem completed_joint_pushforward
    [Fintype I] [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (left : (A × S) → FiniteDistribution (I → A))
    (right : (B × S) → FiniteDistribution (I → B)) (j : I)
    (hleft : ∀ q xs, (left q).weight xs ≠ 0 → xs j = q.1)
    (hright : ∀ q ys, (right q).weight ys ≠ 0 → ys j = q.1)
    (x : A × S) (y : B × S) :
    (seedLaw left right).pushforward
        (fun seed => (completedLeft j seed x, completedRight j seed y)) =
      (left x).product (right y) := by
  apply repaired_joint_pushforward left right
    (fun q xs => Function.update xs j q.1) (fun q ys => Function.update ys j q.1)
  · intro q xs h
    exact update_eq_of_coordinate xs j q.1 (hleft q xs h)
  · intro q ys h
    exact update_eq_of_coordinate ys j q.1 (hright q ys h)

end Completion

end KernelSampling
end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Rectangle
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! An actual finite probability rectangle implementing all thresholds from a
fixed finite list. The seed distribution is shared; each local acceptance test
depends only on its own density. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

theorem rectangle_row_mass (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : density a ∈ thresholds) (h0 : 0 ≤ density a) (h1 : density a ≤ 1) :
    (∑ i, if rectangleAccept thresholds density (a, i) then
      rectangleWeight thresholds (a, i) else 0) = density a / (Fintype.card α : ℝ) := by
  calc
    _ = (∑ i : Fin (thresholdPartition thresholds).length,
        if (thresholdPartition thresholds)[i].lo < density a then
          (thresholdPartition thresholds)[i].hi - (thresholdPartition thresholds)[i].lo else 0) /
        (Fintype.card α : ℝ) := by
      rw [sum_div_const]
      apply Finset.sum_congr rfl
      intro i _
      simp [rectangleAccept, rectangleWeight, ite_div]
    _ = density a / (Fintype.card α : ℝ) := by
      rw [sum_interval_get (fun I => if I.lo < density a then I.hi - I.lo else 0),
        partition_acceptance_mass thresholds (density a) hm h0 h1]

theorem rectangle_acceptance_mass (thresholds : List ℝ) (density : α → ℝ)
    (hm : ∀ a, density a ∈ thresholds) (h0 : ∀ a, 0 ≤ density a)
    (h1 : ∀ a, density a ≤ 1) :
    eventMass (rectangleWeight thresholds) (rectangleAccept thresholds density) =
      (∑ a, density a) / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  simp_rw [rectangle_row_mass thresholds density _ (hm _) (h0 _) (h1 _)]
  rw [sum_div_const]

theorem rectangle_label_mass [DecidableEq α] (thresholds : List ℝ) (density : α → ℝ) (a : α)
    (hm : ∀ x, density x ∈ thresholds) (h0 : ∀ x, 0 ≤ density x)
    (h1 : ∀ x, density x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds density seed && decide (seed.1 = a)) =
      density a / (Fintype.card α : ℝ) := by
  unfold eventMass
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : α, if x = a then density x / (Fintype.card α : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = a
      · simpa [hx] using rectangle_row_mass thresholds density x (hm x) (h0 x) (h1 x)
      · simp [hx]
    _ = density a / (Fintype.card α : ℝ) := by simp

omit [Fintype α] in theorem rectangle_and (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => min (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

omit [Fintype α] in theorem rectangle_or (thresholds : List ℝ) (p q : α → ℝ) :
    (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      rectangleAccept thresholds (fun a => max (p a) (q a)) := by
  funext seed
  simp [rectangleAccept]

theorem min_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : min x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [min_def, h, hx, hy]

theorem max_mem_thresholds (thresholds : List ℝ) {x y : ℝ} (hx : x ∈ thresholds)
    (hy : y ∈ thresholds) : max x y ∈ thresholds := by
  by_cases h : x ≤ y <;> simp [max_def, h, hx, hy]

theorem rectangle_union_mass (thresholds : List ℝ) (p q : α → ℝ)
    (hpm : ∀ a, p a ∈ thresholds) (hqm : ∀ a, q a ∈ thresholds)
    (hp0 : ∀ a, 0 ≤ p a) (_hq0 : ∀ a, 0 ≤ q a)
    (hp1 : ∀ a, p a ≤ 1) (hq1 : ∀ a, q a ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => rectangleAccept thresholds p seed || rectangleAccept thresholds q seed) =
      unionMass p q / (Fintype.card α : ℝ) := by
  rw [rectangle_or]
  exact rectangle_acceptance_mass thresholds _
    (fun a => max_mem_thresholds thresholds (hpm a) (hqm a))
    (fun a => (hp0 a).trans (le_max_left _ _)) (fun a => max_le (hp1 a) (hq1 a))

theorem rectangle_common_label_mass [DecidableEq α] (thresholds : List ℝ)
    (p q : α → ℝ) (a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (_hq1 : ∀ x, q x ≤ 1) :
    eventMass (rectangleWeight thresholds)
      (fun seed => (rectangleAccept thresholds p seed && rectangleAccept thresholds q seed) &&
        decide (seed.1 = a)) = min (p a) (q a) / (Fintype.card α : ℝ) := by
  have hand := congrFun (rectangle_and thresholds p q)
  simp_rw [hand]
  exact rectangle_label_mass thresholds _ a
    (fun x => min_mem_thresholds thresholds (hpm x) (hqm x))
    (fun x => le_min (hp0 x) (hq0 x)) (fun x => (min_le_left _ _).trans (hp1 x))

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_LabelBound
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Per-label diagonal lower bounds for the actual finite shared sampler.
These bounds retain the output label, which is necessary for comparing the
sampler's output distribution with a prescribed diagonal distribution. -/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

noncomputable section

variable {σ α : Type*} [Fintype σ] [DecidableEq σ] [DecidableEq α]

omit [Fintype σ] [DecidableEq σ] in
theorem common_first_label_lower (left right : σ → Bool) (decode : σ → α)
    (fallback a : α) (proposals : List σ) :
    goodFirstIndicator (fun s => left s || right s) (goodLabel left right decode a) proposals ≤
      localDiagonal left right decode fallback a proposals := by
  cases hfirst : firstAccepted (fun s => left s || right s) proposals with
  | none =>
      simp only [goodFirstIndicator, hfirst]
      unfold localDiagonal
      split_ifs <;> norm_num
  | some s =>
      by_cases hc : goodLabel left right decode a s = true
      · have hparts : (left s = true ∧ right s = true) ∧ decode s = a := by
          simpa [goodLabel] using hc
        have h := first_union_common left right proposals s hfirst hparts.1.1 hparts.1.2
        simp [goodFirstIndicator, hfirst, hc, localDiagonal, localSample, h.1, h.2, hparts.2]
      · have hn : 0 ≤ localDiagonal left right decode fallback a proposals := by
          unfold localDiagonal
          split_ifs <;> norm_num
        simpa [goodFirstIndicator, hfirst, hc] using hn

omit [DecidableEq σ] in theorem union_goodLabel_mass
    (w : σ → ℝ) (left right : σ → Bool) (decode : σ → α) (a : α) :
    eventMass w (fun s => (left s || right s) && goodLabel left right decode a s) =
      eventMass w (goodLabel left right decode a) := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro s _
  cases hl : left s <;> cases hr : right s <;> simp [goodLabel, hl, hr]

/-- The finite shared-list sampler's mass on the particular diagonal output
(a,a) is at least the common-first-label mass. Exhaustion uses a fixed local
fallback; its contribution is nonnegative and is not counted in this bound. -/
theorem finite_label_diagonal_bound (w : σ → ℝ) (left right : σ → Bool)
    (decode : σ → α) (fallback a : α) (hw : ∀ s, 0 ≤ w s)
    (hw_sum : ∑ s, w s = 1) (hu : 0 < eventMass w (fun s => left s || right s)) (n : Nat) :
    eventMass w (goodLabel left right decode a) / eventMass w (fun s => left s || right s) *
        (1 - eventMass w (fun s => !(left s || right s)) ^ n) ≤
      traceAverage w n (localDiagonal left right decode fallback a) := by
  have h := traceAverage_mono w hw n _ _ (common_first_label_lower left right decode fallback a)
  rw [goodFirstIndicator_law w _ _ hw_sum n,
    goodFirstMass_exact w _ _ hw_sum (ne_of_gt hu) n,
    union_goodLabel_mass] at h
  exact h

section Rectangle

variable [Fintype α] [Nonempty α]

/-- Concrete normalized-density instance of the per-label bound. All random
proposals come from the finite rectangle constructed from `thresholds`. -/
theorem rectangle_label_diagonal_bound (thresholds : List ℝ) (p q : α → ℝ)
    (fallback a : α)
    (hpm : ∀ x, p x ∈ thresholds) (hqm : ∀ x, q x ∈ thresholds)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x)
    (hp1 : ∀ x, p x ≤ 1) (hq1 : ∀ x, q x ≤ 1)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) (n : Nat) :
    min (p a) (q a) / (1 + totalVariation p q) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds p s || rectangleAccept thresholds q s)) ^ n) ≤
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds p) (rectangleAccept thresholds q)
          Prod.fst fallback a) := by
  have hc : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  have hU : 0 < unionMass p q := by
    rw [unionMass_eq p q hpsum hqsum]
    linarith [totalVariation_nonneg p q]
  have hmass := rectangle_union_mass thresholds p q hpm hqm hp0 hq0 hp1 hq1
  have hu : 0 < eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds p s || rectangleAccept thresholds q s) := by
    rw [hmass]
    exact div_pos hU hc
  have h := finite_label_diagonal_bound (rectangleWeight thresholds)
    (rectangleAccept thresholds p) (rectangleAccept thresholds q) Prod.fst fallback a
    (rectangleWeight_nonnegative thresholds) (rectangleWeight_normalized thresholds) hu n
  unfold goodLabel at h
  rw [rectangle_common_label_mass thresholds p q a hpm hqm hp0 hq0 hp1 hq1, hmass] at h
  have hratio : (min (p a) (q a) / (Fintype.card α : ℝ)) /
      (unionMass p q / (Fintype.card α : ℝ)) = min (p a) (q a) / unionMass p q := by
    field_simp
  rw [hratio, unionMass_eq p q hpsum hqsum] at h
  exact h

end Rectangle

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite shared randomness is an actual convex mixture of distributions. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

theorem probability_mixture_le (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) (bound : ℝ)
    (h : ∀ seed, (laws seed).probability event ≤ bound) :
    (seedLaw.mixture laws).probability event ≤ bound := by
  rw [probability_mixture]
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * bound :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (h seed) (seedLaw.nonnegative seed)
    _ = bound := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

section

/-! Exact finite total variation and its event-probability bound. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- A one-sided event difference is bounded by half the total absolute mass
difference. Normalization is used; the full absolute-mass sum would lose a
factor of two needed in the repetition argument. -/
theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem totalVariation_nonneg (p q : α → ℝ) : 0 ≤ totalVariation p q := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => abs_nonneg (p a - q a))) (by norm_num)

theorem totalVariation_symm (p q : α → ℝ) : totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

end UniqueGamesTheorem.Foundations.Information

end

section

/-!
Conditional laws on finite spaces, with a normalized default on null rows.
The default remains a probability law when a new input law charges a row
that had zero probability in the original joint distribution.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Statistical distance under finite kernels and event restriction. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_joint_common_weights (w : α → ℝ) (p q : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) :
    totalVariation (fun ab : α × β => w ab.1 * p ab.1 ab.2)
      (fun ab : α × β => w ab.1 * q ab.1 ab.2) =
        ∑ a, w a * totalVariation (p a) (q a) := by
  have hpoint : ∀ a b, |w a * p a b - w a * q a b| = w a * |p a b - q a b| := by
    intro a b
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw a)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SharedProfiles
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
A single finite rectangle proposal law for two finite families of distributions.
The subdivision includes every density appearing in either family.  Consequently
the local samplers share a seed space independently of their particular inputs.
-/

namespace UniqueGamesTheorem.Foundations.CorrelatedSampling

open scoped BigOperators

noncomputable section

theorem mem_profileThresholds {κ S : Type*} [Fintype κ] [Fintype S]
    (P : κ → S → ℝ) (k : κ) (s : S) : P k s ∈ profileThresholds P := by
  classical
  exact List.mem_map.mpr ⟨(k, s), by simp, rfl⟩

theorem distribution_weight_le_one {S : Type*} [Fintype S]
    (μ : Games.FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

variable {Q₁ Q₂ S : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype S]

theorem left_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (x : Q₁) (s : S) :
    (L x).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inl x) s

theorem right_mem_sharedProfileThresholds (L : Q₁ → Games.FiniteDistribution S)
    (R : Q₂ → Games.FiniteDistribution S) (y : Q₂) (s : S) :
    (R y).weight s ∈ sharedProfileThresholds L R := by
  exact mem_profileThresholds _ (Sum.inr y) s

theorem uniformRejectionRate_nonnegative (S : Type*) [Fintype S] [Nonempty S] :
    0 ≤ uniformRejectionRate S := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hc₁ : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card S))
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hc).2 (by simpa using hc₁)

theorem uniformRejectionRate_lt_one (S : Type*) [Fintype S] [Nonempty S] :
    uniformRejectionRate S < 1 := by
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hp : (0 : ℝ) < 1 / (Fintype.card S : ℝ) := div_pos (by norm_num) hc
  dsimp [uniformRejectionRate]
  linarith

theorem sharedProfileReject_nonnegative [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : 0 ≤ sharedProfileReject L R x y := by
  exact eventMass_nonneg _ _
    (rectangleDistribution (α := S) (sharedProfileThresholds L R)).nonnegative

theorem sharedProfile_reject_le_rate [Nonempty S]
    (L : Q₁ → Games.FiniteDistribution S) (R : Q₂ → Games.FiniteDistribution S)
    (x : Q₁) (y : Q₂) : sharedProfileReject L R x y ≤ uniformRejectionRate S := by
  let thresholds := sharedProfileThresholds L R
  have hsum : (∑ s : RectangleSeed thresholds S, rectangleWeight thresholds s) = 1 :=
    (rectangleDistribution (α := S) thresholds).normalized
  have hcomp := eventMass_complement (rectangleWeight thresholds)
    (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) hsum
  have hu : eventMass (rectangleWeight thresholds)
      (fun s => sharedProfileLeft L R x s || sharedProfileRight L R y s) =
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) := by
    change eventMass (rectangleWeight thresholds)
      (fun s => rectangleAccept thresholds (L x).weight s ||
        rectangleAccept thresholds (R y).weight s) = _
    rw [rectangle_union_mass thresholds (L x).weight (R y).weight
      (left_mem_sharedProfileThresholds L R x)
      (right_mem_sharedProfileThresholds L R y)
      (L x).nonnegative (R y).nonnegative
      (distribution_weight_le_one (L x)) (distribution_weight_le_one (R y))]
    rw [unionMass_eq (L x).weight (R y).weight (L x).normalized (R y).normalized]
  have hc : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have htv := totalVariation_nonneg (L x).weight (R y).weight
  have hquot : 1 / (Fintype.card S : ℝ) ≤
      (1 + totalVariation (L x).weight (R y).weight) / (Fintype.card S : ℝ) :=
    (div_le_div_iff_of_pos_right hc).2 (by linarith)
  rw [hu] at hcomp
  change eventMass (rectangleWeight thresholds)
    (fun s => !(sharedProfileLeft L R x s || sharedProfileRight L R y s)) ≤
      1 - 1 / (Fintype.card S : ℝ)
  linarith

theorem exists_uniformRejectionRate_pow_lt (S : Type*) [Fintype S] [Nonempty S]
    (η : ℝ) (hη : 0 < η) : ∃ n : ℕ, uniformRejectionRate S ^ n < η := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (uniformRejectionRate_nonnegative S) (uniformRejectionRate_lt_one S)
  exact (ht.eventually (gt_mem_nhds hη)).exists

end

end UniqueGamesTheorem.Foundations.CorrelatedSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FactorizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The finite product algebra of dependency breaking.

Revealing one endpoint of each independently sampled question pair turns the
remaining question weight into a product of two separate functions, one for
each player. Further separate restrictions on the players' answers preserve
this product. The final theorem normalizes the displayed weights, rather than
assuming conditional independence as an abstract hypothesis.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq α] [DecidableEq β]

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem productWeight_mass (left : X → ℝ) (right : Y → ℝ) :
    (∑ xy : X × Y, left xy.1 * right xy.2) =
      (∑ x, left x) * (∑ y, right y) := by
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

end

end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Normalized local completion laws derived from their actual product weights.
Zero rows use explicit default laws and satisfy the same recombination identity.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem sum_mul_normalizeOr (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (fallback : FiniteDistribution X) (x : X) :
    (∑ z, w z) * (normalizeOr w hw fallback).weight x = w x := by
  classical
  have hs : 0 ≤ ∑ z, w z := Finset.sum_nonneg (fun z _ => hw z)
  by_cases h : 0 < ∑ z, w z
  · simp only [normalizeOr, dite_eq_left h, normalizedWeight]
    field_simp
  · have hz : ∑ z, w z = 0 := le_antisymm (le_of_not_gt h) hs
    have hx : w x = 0 := by
      apply le_antisymm _ (hw x)
      have hl := Finset.single_le_sum (fun z _ => hw z) (Finset.mem_univ x)
      simpa only [hz] using hl
    simp [normalizeOr, hz, hx]

/-- Exact reconstruction from two separately normalized local completion
laws, valid even when either unnormalized row has mass zero. -/
theorem local_completion_recombination
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (x : X) (y : Y) :
    (c * (∑ z, left z) * (∑ z, right z)) *
      ((normalizeOr left hl defaultLeft).weight x *
        (normalizeOr right hr defaultRight).weight y) = c * left x * right y := by
  calc
    _ = c * ((∑ z, left z) * (normalizeOr left hl defaultLeft).weight x) *
        ((∑ z, right z) * (normalizeOr right hr defaultRight).weight y) := by ring
    _ = _ := by rw [sum_mul_normalizeOr, sum_mul_normalizeOr]

/-- The row mass appearing in reconstruction is the actual sum of product
weights, not an assumed marginal identity. -/
theorem factorized_completion_row
    (left : X → ℝ) (right : Y → ℝ)
    (hl : ∀ x, 0 ≤ left x) (hr : ∀ y, 0 ≤ right y)
    (defaultLeft : FiniteDistribution X) (defaultRight : FiniteDistribution Y)
    (c : ℝ) (xy : X × Y) :
    (∑ z : X × Y, c * left z.1 * right z.2) *
      ((normalizeOr left hl defaultLeft).product
        (normalizeOr right hr defaultRight)).weight xy = c * left xy.1 * right xy.2 := by
  have hm : (∑ z : X × Y, c * left z.1 * right z.2) =
      c * (∑ z, left z) * (∑ z, right z) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [productWeight_mass]
  rw [hm]
  exact local_completion_recombination left right hl hr defaultLeft defaultRight c xy.1 xy.2

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-!
Local embedding to single-game strategy transfer for Holenstein's argument.
The embedding law below is explicitly sampled from a finite shared seed and
the base game's actual joint question law. Its distance from the desired
conditioned law is an explicit total-variation expression. Constructing an
embedding with a sufficiently small distance is a separate proof obligation.
-/

namespace UniqueGamesTheorem.Foundations.Games.Game

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ Seed : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype Seed]
  [Nonempty A₁] [Nonempty A₂]

/-- Any finite shared-randomness local embedding yields a valid base-game
strategy after the seed is fixed. Total variation pays exactly for changing
the resulting question distribution to the desired one. -/
theorem success_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → R₁) (right : Seed → Q₂ → R₂)
    (answerLeft : Seed → Q₁ → B₁ → A₁)
    (answerRight : Seed → Q₂ → B₂ → A₂)
    (acceptance : ∀ seed x y a b,
      H.accepts (left seed x) (right seed y) a b = true →
      G.accepts x y (answerLeft seed x a) (answerRight seed y b) = true)
    (strategy : Strategy R₁ R₂ B₁ B₂) :
    H.success strategy ≤ G.value +
      H.questions.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  have localBound (seed : Seed) :
      (G.questions.pushforward (fun q => (left seed q.1, right seed q.2))).probability
        (H.wins strategy) ≤ G.value := by
    let embedded : Game R₁ R₂ B₁ B₂ :=
      { questions := G.questions.pushforward fun q => (left seed q.1, right seed q.2)
        accepts := H.accepts }
    change embedded.success strategy ≤ G.value
    exact (G.success_le_of_localSimulation embedded (left seed) (right seed)
      (answerLeft seed) (answerRight seed) rfl (acceptance seed) strategy).trans
      (G.success_le_value _)
  have mixtureBound :
      (G.localEmbeddingLaw seedLaw left right).probability (H.wins strategy) ≤ G.value :=
    seedLaw.probability_mixture_le _ _ _ localBound
  exact (H.questions.probability_le_add_totalVariation
    (G.localEmbeddingLaw seedLaw left right) (H.wins strategy)).trans
    (add_le_add mixtureBound (le_refl _))

/-- The strategy-extraction step used for a surviving coordinate after
conditioning on successes at other coordinates. It preserves full local
question dependence and uses no independence assumption on the target law. -/
theorem coordinate_probability_le_value_add_embedding_distance
    (G : Game Q₁ Q₂ A₁ A₂) {n : Nat} (coordinate : Fin n)
    (law : FiniteDistribution ((Fin n → Q₁) × (Fin n → Q₂)))
    (seedLaw : FiniteDistribution Seed)
    (left : Seed → Q₁ → Fin n → Q₁) (right : Seed → Q₂ → Fin n → Q₂)
    (left_preserves : ∀ seed x, left seed x coordinate = x)
    (right_preserves : ∀ seed y, right seed y coordinate = y)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂)) :
    law.probability (G.coordinateWin strategy coordinate) ≤ G.value +
      law.totalVariation (G.localEmbeddingLaw seedLaw left right) := by
  apply G.success_le_value_add_embedding_distance (G.coordinateGame coordinate law)
    seedLaw left right (fun _ _ a => a coordinate) (fun _ _ b => b coordinate)
  intro seed x y a b h
  simpa only [coordinateGame, left_preserves, right_preserves] using h

end
end UniqueGamesTheorem.Foundations.Games.Game

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact composition identities for finite distribution maps. -/
namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_Variation
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite total-variation operations used by the dependency-breaking argument.
All statements concern the displayed real weight functions. In particular,
conditioning rescales actual restricted weights, and kernels act by finite sums.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

theorem totalVariation_triangle (p q r : α → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hpoint : ∀ a, |p a - r a| ≤ |p a - q a| + |q a - r a| := by
    intro a
    have := abs_add_le (p a - q a) (q a - r a)
    simpa only [sub_add_sub_cancel] using this
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [Finset.sum_add_distrib] at hsum
  unfold totalVariation
  linarith

theorem totalVariation_kernelPushforward_le (p q : α → ℝ) (kernel : α → β → ℝ)
    (hk : ∀ a, IsProbability (kernel a)) :
    totalVariation (kernelPushforward p kernel) (kernelPushforward q kernel) ≤
      totalVariation p q := by
  have hpoint : ∀ b,
      |kernelPushforward p kernel b - kernelPushforward q kernel b| ≤
        ∑ a, |p a - q a| * kernel a b := by
    intro b
    simp only [kernelPushforward, ← Finset.sum_sub_distrib, ← sub_mul]
    have h := Finset.abs_sum_le_sum_abs (fun a => (p a - q a) * kernel a b) Finset.univ
    have habs : ∀ a, |kernel a b| = kernel a b := fun a => abs_of_nonneg ((hk a).1 b)
    simpa only [abs_mul, habs] using h
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset β)) => hpoint b)
  rw [Finset.sum_comm] at hsum
  simp only [← Finset.mul_sum, (hk _).2, mul_one] at hsum
  exact div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedInformationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Identification of the auxiliary selected-answer/reveal law with the actual
repeated-game question law conditioned on selected-coordinate success.
The proof sums out answer labels and reveal variables before merging the
selected and unselected question coordinates.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games Information
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedSplit_question_probability (G : Game Q₁ Q₂ A₁ A₂)
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedSplitLaw G selected).probability
      (fun q => event (selectedQuestionTuple selected q.1 q.2)) =
        (G.repetition n).questions.probability event := by
  rw [selectedSplitLaw, ← iid_coordinate_split, FiniteDistribution.probability_transport]
  change (G.questions.iid n).probability _ =
    ((G.questions.iid n).transport (Game.tupleQuestionEquiv n)).probability event
  rw [FiniteDistribution.probability_transport]
  apply congrArg (G.questions.iid n).probability
  funext q
  congr 1
  apply Prod.ext <;> funext i <;>
    simp [selectedQuestionTuple, coordinateSplitEquiv, mergeCoordinates, Game.tupleQuestionEquiv]

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The selected-success likelihood factors into a fixed verifier check and
two separate tests on the local deterministic answers. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_left (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).1 =
      mergeCoordinates selected (fun i => (fixed i).1) (fun i => (remaining i).1) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [Fintype Q₁] [Fintype Q₂] [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedQuestionTuple_right (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂) (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (selectedQuestionTuple selected fixed remaining).2 =
      mergeCoordinates selected (fun i => (fixed i).2) (fun i => (remaining i).2) := by
  funext i
  simp only [selectedQuestionTuple, mergeCoordinates]
  split <;> rfl

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedWins_of_answerLabel (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂)
    (hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label) :
    G.selectedWins strategy selected (selectedQuestionTuple selected fixed remaining) =
      selectedLabelAccepts G selected fixed label := by
  classical
  have hleft (i : selected) := congrArg (fun l => l.1 i) hlabel
  have hright (i : selected) := congrArg (fun l => l.2 i) hlabel
  apply Bool.eq_iff_iff.mpr
  simp only [Game.selectedWins, selectedLabelAccepts, decide_eq_true_eq]
  constructor
  · intro h i
    have hi := h i.1 i.property
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, i.property,
      ← hleft i, ← hright i, selectedAnswerLabel] using hi
  · intro h i hi
    have hv := h ⟨i,hi⟩
    simpa [Game.coordinateWin, selectedQuestionTuple, mergeCoordinates, hi,
      ← hleft ⟨i,hi⟩, ← hright ⟨i,hi⟩, selectedAnswerLabel] using hv

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedLikelihood_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (fixed : selected → Q₁ × Q₂)
    (label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    selectedLikelihood G strategy selected fixed label remaining =
      (if selectedLabelAccepts G selected fixed label then 1 else 0) *
        selectedLocalTest strategy.1 selected (fun i => (fixed i).1) label.1 (fun i => (remaining i).1) *
        selectedLocalTest strategy.2 selected (fun i => (fixed i).2) label.2 (fun i => (remaining i).2) := by
  classical
  have he : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) =
      (selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1) (fun i => (remaining i).1),
       selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2) (fun i => (remaining i).2)) := by
    simp only [selectedAnswerLabel,
      selectedQuestionTuple_left, selectedQuestionTuple_right]
    rfl
  by_cases hl : selectedLocalAnswers strategy.1 selected (fun i => (fixed i).1)
      (fun i => (remaining i).1) = label.1
  · by_cases hr : selectedLocalAnswers strategy.2 selected (fun i => (fixed i).2)
        (fun i => (remaining i).2) = label.2
    · have hlabel : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) = label := by
        rw [he, hl, hr]
      simp only [selectedLikelihood, ite_eq_left hlabel,
        selectedWins_of_answerLabel G strategy selected fixed label remaining hlabel,
        selectedLocalTest, ite_eq_left hl, ite_eq_left hr, mul_one]
    · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
        intro h
        rw [he] at h
        exact hr (congrArg Prod.snd h)
      simp [selectedLikelihood, hn, selectedLocalTest, hl, hr]
  · have hn : selectedAnswerLabel strategy selected (selectedQuestionTuple selected fixed remaining) ≠ label := by
      intro h
      rw [he] at h
      exact hl (congrArg Prod.fst h)
    simp [selectedLikelihood, hn, selectedLocalTest, hl]

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_PartialRevealLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Removing one independent reveal from the explicit product law. The
likelihood can be any function of the questions and outside data. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem totalVariation_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p q : B → ℝ) :
    Information.totalVariation (fun a => p (e a)) (fun a => q (e a)) =
      Information.totalVariation p q := by
  unfold Information.totalVariation
  congr 1
  exact e.sum_comp (fun b => |p b - q b|)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual sum-tagged reveal law separates into local endpoint factors.
The fair reveal probability is retained in those factors. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem revealLaw_factorization (μ : FiniteDistribution (X × Y))
    (r : X ⊕ Y) (x : X) (y : Y) :
    (revealLaw μ).weight ((x,y),r) =
      revealLeftFactor μ r x * revealRightFactor μ r y := by
  rw [revealLaw_weight]
  cases r with
  | inl u =>
    by_cases h : x = u
    · subst x; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]
  | inr v =>
    by_cases h : y = v
    · subst y; simp [revealLeftFactor, revealRightFactor]
    · simp [revealLeftFactor, revealRightFactor, h, Ne.symm h]

theorem partialRevealWeight_factorization (μ : FiniteDistribution (X × Y)) (j : I)
    (rest : {i : I // i ≠ j} → X ⊕ Y) (u : I → X × Y) :
    partialRevealWeight μ j rest u =
      μ.weight (u j) * partialLeftFactor μ j rest (fun i => (u i).1) *
        partialRightFactor μ j rest (fun i => (u i).2) := by
  have hpoint (i : {i : I // i ≠ j}) :
      (revealLaw μ).weight (u i.1,rest i) =
        revealLeftFactor μ (rest i) (u i.1).1 * revealRightFactor μ (rest i) (u i.1).2 :=
    revealLaw_factorization μ (rest i) (u i.1).1 (u i.1).2
  simp only [partialRevealWeight, partialLeftFactor, partialRightFactor,
    hpoint, Finset.prod_mul_distrib]
  ring

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_Overlap
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Direct diagonal-overlap comparison for the finite correlated sampler.
All quantities are finite weight arrays; no reference sampler or embedding
claim is assumed. The final theorem consumes the per-label lower bound that
is proved for the actual finite threshold sampler in CorrelatedSampling.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Information

private theorem min_half_formula (x y : ℝ) :
    min x y = (x + y - |x - y|) / 2 := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem sum_min_one_sub_tv {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp : IsProbability p) (hq : IsProbability q) :
    (∑ z, min (p z) (q z)) = 1 - totalVariation p q := by
  classical
  simp_rw [min_half_formula]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.2, hq.2, totalVariation]
  ring

private theorem discount_le_self {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c / (1 + t) ≤ c := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + t)).2
  nlinarith [mul_nonneg hc ht]

private theorem discount_loss_le_mul {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    c - c / (1 + t) ≤ c * t := by
  have hd : 0 < 1 + t := by linarith
  have hid : c - c / (1 + t) = c * t / (1 + t) := by
    field_simp [hd.ne']
    ring
  rw [hid]
  apply (div_le_iff₀ hd).2
  nlinarith [mul_nonneg (mul_nonneg hc ht) ht]

/-- The direct common-mass argument, with its exact finite-array premises. -/
theorem discounted_common_mass_bounds {X S : Type*} [Fintype X] [Fintype S]
    (p a b : X × S → ℝ) (μ t : X → ℝ)
    (hp : IsProbability p) (ha : IsProbability a) (hb : IsProbability b)
    (ht : ∀ x, 0 ≤ t x)
    (hrow : ∀ x, (∑ s, a (x, s)) = μ x)
    (htv : (∑ x, μ x * t x) = totalVariation a b) :
    1 - 2 * totalVariation p a - 2 * totalVariation p b ≤ discountedCommonMass p a b t ∧
      discountedCommonMass p a b t ≤ 1 := by
  classical
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have hC0 : ∀ z, 0 ≤ C z := by
    intro z
    exact le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
  have hCp : ∀ z, C z ≤ p z := by
    intro z
    exact min_le_left _ _
  have hCa : ∀ z, C z ≤ a z := by
    intro z
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hmass : 1 - totalVariation p a - totalVariation p b ≤ ∑ z, C z := by
    have hpoint : ∀ z, min (p z) (a z) + min (p z) (b z) - p z ≤ C z := by
      intro z
      dsimp [C]
      refine le_min ?_ (le_min ?_ ?_)
      · linarith [min_le_left (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (a z), min_le_left (p z) (b z)]
      · linarith [min_le_right (p z) (b z), min_le_left (p z) (a z)]
    have hsum := Finset.sum_le_sum
      (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
    rw [sum_min_one_sub_tv p a hp ha, sum_min_one_sub_tv p b hp hb, hp.2] at hsum
    linarith
  have hrowC : ∀ x, (∑ s, C (x, s)) ≤ μ x := by
    intro x
    calc
      (∑ s, C (x, s)) ≤ ∑ s, a (x, s) := Finset.sum_le_sum (fun s _ => hCa (x, s))
      _ = μ x := hrow x
  have hweighted : (∑ z, C z * t z.1) ≤ totalVariation a b := by
    rw [← htv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro x _
    change (∑ s, C (x, s) * t x) ≤ μ x * t x
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrowC x) (ht x)
  have hloss : (∑ z, C z) - discountedCommonMass p a b t ≤ ∑ z, C z * t z.1 := by
    change (∑ z, C z) - (∑ z, C z / (1 + t z.1)) ≤ ∑ z, C z * t z.1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun z _ => discount_loss_le_mul (hC0 z) (ht z.1))
  have htriangle : totalVariation a b ≤ totalVariation p a + totalVariation p b := by
    have h := totalVariation_triangle a p b
    rw [totalVariation_symm a p] at h
    exact h
  have hupper : discountedCommonMass p a b t ≤ 1 := by
    change (∑ z, C z / (1 + t z.1)) ≤ 1
    calc
      _ ≤ ∑ z, p z := Finset.sum_le_sum
        (fun z _ => (discount_le_self (hC0 z) (ht z.1)).trans (hCp z))
      _ = 1 := hp.2
  exact ⟨by linarith, hupper⟩

theorem diagonal_overlap_identity {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (sim : X × S × S → ℝ)
    (hp : IsProbability p) (hsim : IsProbability sim) :
    totalVariation sim (diagonalWeights p) =
      1 - ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
  classical
  have h := sum_min_one_sub_tv sim (diagonalWeights p) hsim (diagonalWeights_isProbability p hp)
  have heq : (∑ z, min (sim z) (diagonalWeights p z)) =
      ∑ z : X × S, min (p z) (sim (z.1, z.2, z.2)) := by
    simp only [Fintype.sum_prod_type, diagonalWeights]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro s _
    have hpoint : ∀ s', min (sim (x, s, s')) (if s = s' then p (x, s) else 0) =
        if s = s' then min (p (x, s)) (sim (x, s, s')) else 0 := by
      intro s'
      by_cases he : s = s'
      · simp [he, min_comm]
      · simp [he, min_eq_right (hsim.1 (x, s, s'))]
    simp only [hpoint]
    simp
  rw [heq] at h
  linarith

/-- The per-label diagonal guarantee implies direct TV control even when the
target's question marginal differs from the simulator's question marginal. -/
theorem diagonal_sampler_totalVariation_le {X S : Type*} [Fintype X] [Fintype S]
    (p : X × S → ℝ) (μ : X → ℝ) (L R : X → S → ℝ)
    (sim : X × S × S → ℝ) (hp : IsProbability p) (hμ : IsProbability μ)
    (hL : ∀ x, IsProbability (L x)) (hR : ∀ x, IsProbability (R x))
    (hsim : IsProbability sim) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hdiag : ∀ x s, μ x * min (L x s) (R x s) /
      (1 + totalVariation (L x) (R x)) * (1 - τ) ≤ sim (x, s, s)) :
    totalVariation sim (diagonalWeights p) ≤
      2 * totalVariation p (fun z => μ z.1 * L z.1 z.2) +
      2 * totalVariation p (fun z => μ z.1 * R z.1 z.2) + τ := by
  classical
  let a : X × S → ℝ := fun z => μ z.1 * L z.1 z.2
  let b : X × S → ℝ := fun z => μ z.1 * R z.1 z.2
  let t : X → ℝ := fun x => totalVariation (L x) (R x)
  let C : X × S → ℝ := fun z => min (p z) (min (a z) (b z))
  have ha : IsProbability a := kernelProduct_isProbability μ L hμ hL
  have hb : IsProbability b := kernelProduct_isProbability μ R hμ hR
  have ht : ∀ x, 0 ≤ t x := fun x => totalVariation_nonneg (L x) (R x)
  have hrow : ∀ x, (∑ s, a (x, s)) = μ x := by
    intro x
    simp only [a, ← Finset.mul_sum, (hL x).2, mul_one]
  have htv : (∑ x, μ x * t x) = totalVariation a b :=
    (totalVariation_joint_common_weights μ L R hμ.1).symm
  obtain ⟨hBlower, hBupper⟩ := discounted_common_mass_bounds p a b μ t hp ha hb ht hrow htv
  have hpoint : ∀ z : X × S,
      (1 - τ) * (C z / (1 + t z.1)) ≤ min (p z) (sim (z.1, z.2, z.2)) := by
    intro z
    have hden : 0 < 1 + t z.1 := by linarith [ht z.1]
    have hC0 : 0 ≤ C z := le_min (hp.1 z) (le_min (ha.1 z) (hb.1 z))
    have hCp : C z ≤ p z := min_le_left _ _
    have hdisc0 : 0 ≤ C z / (1 + t z.1) := div_nonneg hC0 hden.le
    have hmin : min (a z) (b z) = μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      dsimp [a, b]
      rcases le_total (L z.1 z.2) (R z.1 z.2) with h | h
      · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
      · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h (hμ.1 z.1))]
    have hCmin : C z ≤ μ z.1 * min (L z.1 z.2) (R z.1 z.2) := by
      rw [← hmin]
      exact min_le_right _ _
    apply le_min
    · calc
        _ ≤ 1 * (C z / (1 + t z.1)) :=
          mul_le_mul_of_nonneg_right (by linarith) hdisc0
        _ ≤ C z := by simpa using discount_le_self hC0 (ht z.1)
        _ ≤ p z := hCp
    · have hd := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hCmin hden.le) (by linarith : 0 ≤ 1 - τ)
      calc
        _ ≤ (1 - τ) * (μ z.1 * min (L z.1 z.2) (R z.1 z.2) / (1 + t z.1)) := hd
        _ ≤ sim (z.1, z.2, z.2) := by
          simpa only [t, mul_comm] using hdiag z.1 z.2
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (X × S))) => hpoint z)
  rw [← Finset.mul_sum] at hsum
  change (1 - τ) * discountedCommonMass p a b t ≤ _ at hsum
  rw [diagonal_overlap_identity p sim hp hsim]
  have hτB := mul_le_mul_of_nonneg_left hBupper hτ0
  change 1 - _ ≤ 2 * totalVariation p a + 2 * totalVariation p b + τ
  nlinarith

end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_SelectedCommonMarginalLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Actual local completions of the unused questions, conditioned on common data
and the player's own embedded question. The raw row factors are explicit
finite weights. Their normalization reconstructs the actual selected common
law, including zero rows. The fallback independently samples base marginal
questions and then inserts the local input at the embedded coordinate.
-/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

section LocalNormalization

variable {I X Y : Type*} [Fintype I] [DecidableEq I]
  [Fintype X] [Fintype Y]

theorem updatedTableFallback_zero (μ : FiniteDistribution X) (j : I) (x : X)
    (l : I → X) (hne : l j ≠ x) :
    (updatedTableFallback μ j x).weight l = 0 := by
  classical
  simp only [updatedTableFallback, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  apply ite_eq_right
  intro h
  have he := congrFun h j
  exact hne (by simpa only [Function.update_self] using he.symm)

theorem normalizeOr_weight_eq_zero_of_zero
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (fallback : FiniteDistribution X)
    (x : X) (hraw : w x = 0) (hdefault : fallback.weight x = 0) :
    (normalizeOr w hw fallback).weight x = 0 := by
  classical
  unfold normalizeOr
  split
  · change normalizedWeight w x = 0
    simp only [normalizedWeight, hraw, zero_div]
  · exact hdefault

end LocalNormalization

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₂] in
theorem selectedLeftCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (x : Q₁) (l : {i : Fin n // i ∉ selected} → Q₁) (hne : l j ≠ x) :
    (selectedLeftCompletion G strategy selected j s x).weight l = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedLeftRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j x l hne

omit [DecidableEq Q₁] in
theorem selectedRightCompletion_zero (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (y : Q₂) (r : {i : Fin n // i ∉ selected} → Q₂) (hne : r j ≠ y) :
    (selectedRightCompletion G strategy selected j s y).weight r = 0 := by
  apply normalizeOr_weight_eq_zero_of_zero
  · simp only [selectedRightRaw, ite_eq_right hne, zero_mul]
  · exact updatedTableFallback_zero _ j y r hne

/-- Pointwise factorization of the actual selected common-data row. -/
theorem selected_completion_factorization (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r =
      if (l j, r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rcases xy with ⟨x,y⟩
  by_cases hl : l j = x <;> by_cases hr : r j = y
  · rw [ite_eq_left (Prod.ext hl hr), partialRevealWeight_factorization]
    cases hacc : selectedLabelAccepts G selected s.1.1 s.1.2 <;>
      simp [selectedOutsideLikelihood, selectedLikelihood_factorization,
        selectedCompletionScale, selectedLeftRaw, selectedRightRaw, hl, hr, hacc]
    ring
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]
  · simp [selectedLeftRaw, selectedRightRaw, hl, hr, Prod.mk.injEq]

theorem selectedCommonLaw_completion_row_mass (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) =
      ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) ×
          ({i : Fin n // i ∉ selected} → Q₂),
        selectedCompletionScale G strategy selected j s xy *
          selectedLeftRaw G strategy selected j s xy.1 lr.1 *
          selectedRightRaw G strategy selected j s xy.2 lr.2 := by
  classical
  change (∑ u, if u j = xy then partialRevealWeight G.questions j s.2 u *
    selectedOutsideLikelihood G strategy selected s.1 u else 0) = _
  rw [← (completionTupleEquiv (I := {i : Fin n // i ∉ selected})
    (X := Q₁) (Y := Q₂)).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  exact (selected_completion_factorization G strategy selected j s xy
    (fun i => (u i).1) (fun i => (u i).2)).symm

/-- Actual common-row mass times the two local completion probabilities is
the selected partial-reveal weight with its actual coordinate indicator. -/
theorem selected_completion_row_recombine (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂)
    (l : {i : Fin n // i ∉ selected} → Q₁)
    (r : {i : Fin n // i ∉ selected} → Q₂) :
    (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight (l,r) =
      if (l j,r j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (l i,r i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (l i,r i))
      else 0 := by
  rw [selectedCommonLaw_completion_row_mass]
  calc
    _ = selectedCompletionScale G strategy selected j s xy *
        selectedLeftRaw G strategy selected j s xy.1 l *
        selectedRightRaw G strategy selected j s xy.2 r :=
      factorized_completion_row
        (selectedLeftRaw G strategy selected j s xy.1)
        (selectedRightRaw G strategy selected j s xy.2)
        (selectedLeftRaw_nonnegative G strategy selected j s xy.1)
        (selectedRightRaw_nonnegative G strategy selected j s xy.2)
        (updatedTableFallback (G.questions.pushforward Prod.fst) j xy.1)
        (updatedTableFallback (G.questions.pushforward Prod.snd) j xy.2)
        (selectedCompletionScale G strategy selected j s xy) (l,r)
    _ = _ := selected_completion_factorization G strategy selected j s xy l r

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The actual local completion mixture reproduces the repeated question law
conditioned on the selected wins. All hidden coordinates and reveal variables
are explicitly summed out. -/

namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section

theorem partialRevealWeight_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (u : I → X × Y) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y, partialRevealWeight μ j rest u) =
      ∏ i, μ.weight (u i) := by
  have h := reveal_product_forget μ (fun i : {i : I // i ≠ j} => u i.1)
  simp_rw [reveal_product_factorization] at h
  simp only [partialRevealWeight, ← Finset.mul_sum]
  rw [h]
  exact (Fintype.prod_eq_mul_prod_subtype_ne (fun i => μ.weight (u i)) j).symm

theorem partialReveal_event_forget
    {I X Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteDistribution (X × Y)) (j : I) (f : (I → X × Y) → ℝ) :
    (∑ rest : {i : I // i ≠ j} → X ⊕ Y,
      ∑ u : I → X × Y, partialRevealWeight μ j rest u * f u) =
      ∑ u, (∏ i, μ.weight (u i)) * f u := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul, partialRevealWeight_forget]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

omit [DecidableEq Q₁] [DecidableEq Q₂] in
theorem selectedOutsideLikelihood_event_sum (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n))
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (∏ i, G.questions.weight (u i)) * selectedOutsideLikelihood G strategy selected t u *
          (if event (selectedQuestionTuple selected t.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  classical
  have hlabel (fixed : selected → Q₁ × Q₂)
      (u : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
      (∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
        (∏ i, G.questions.weight (u i)) *
          selectedOutsideLikelihood G strategy selected (fixed,label) u *
            (if event (selectedQuestionTuple selected fixed u) then 1 else 0)) =
      ((∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
        (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
          event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
            G.selectedSuccess strategy selected := by
    calc
      _ = (∏ i, G.questions.weight (u i)) *
          (∏ i : selected, G.questions.weight (fixed i)) *
          (∑ label, selectedLikelihood G strategy selected fixed label u) *
          (if event (selectedQuestionTuple selected fixed u) then 1 else 0) /
            G.selectedSuccess strategy selected := by
        simp only [selectedOutsideLikelihood, div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro label _
        ring
      _ = _ := by
        rw [selectedLikelihood_sum]
        cases hw : G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) <;>
          cases he : event (selectedQuestionTuple selected fixed u) <;> simp
        ring
  calc
    _ = ∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          ∑ label : SelectedLabels (A₁ := A₁) (A₂ := A₂) selected,
            (∏ i, G.questions.weight (u i)) *
              selectedOutsideLikelihood G strategy selected (fixed,label) u *
                (if event (selectedQuestionTuple selected fixed u) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro fixed _
      rw [Finset.sum_comm]
    _ = (∑ fixed : selected → Q₁ × Q₂,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          (∏ i : selected, G.questions.weight (fixed i)) * (∏ i, G.questions.weight (u i)) *
            (if G.selectedWins strategy selected (selectedQuestionTuple selected fixed u) &&
              event (selectedQuestionTuple selected fixed u) then 1 else 0)) /
                G.selectedSuccess strategy selected := by
      simp_rw [hlabel]
      simp only [div_eq_mul_inv, Finset.sum_mul]
    _ = _ := by
      congr 1
      have h := selectedSplit_question_probability G selected
        (fun q => G.selectedWins strategy selected q && event q)
      simpa [selectedSplitLaw, FiniteDistribution.probability, FiniteDistribution.product,
        FiniteDistribution.table, Fintype.sum_prod_type, mul_ite] using h

theorem selected_partial_event_total (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0)) =
      (G.repetition n).questions.probability
        (fun q => G.selectedWins strategy selected q && event q) /
          G.selectedSuccess strategy selected := by
  have hrest (t : (selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) :=
    partialReveal_event_forget G.questions j
      (fun u => selectedOutsideLikelihood G strategy selected t u *
        (if event (selectedQuestionTuple selected t.1 u) then 1 else 0))
  simp only [← mul_assoc] at hrest
  rw [Fintype.sum_prod_type]
  simp_rw [hrest]
  exact selectedOutsideLikelihood_event_sum G strategy selected event

omit [DecidableEq Q₂] in
theorem selectedFullLeftCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₁ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (l : Fin n → Q₁) (h : (selectedFullLeftCompletion G strategy selected j q).weight l ≠ 0) :
    l j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullLeftCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedLeftCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

omit [DecidableEq Q₁] in
theorem selectedFullRightCompletion_support (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (q : Q₂ × SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (r : Fin n → Q₂) (h : (selectedFullRightCompletion G strategy selected j q).weight r ≠ 0) :
    r j.1 = q.1 := by
  classical
  by_contra hne
  apply h
  simp only [selectedFullRightCompletion, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro t _
  split
  · rename_i he
    apply selectedRightCompletion_zero
    intro ht
    apply hne
    have hcoord := congrFun he j.1
    simpa [mergeCoordinates, j.property, ht] using hcoord.symm
  · rfl

theorem selected_full_completion_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (xy : Q₁ × Q₂) (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
      (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event =
    ∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
      ((selectedLeftCompletion G strategy selected j s xy.1).product
        (selectedRightCompletion G strategy selected j s xy.2)).weight lr *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)))
            then 1 else 0) := by
  rw [selectedFullLeftCompletion, selectedFullRightCompletion,
    ← FiniteDistribution.product_pushforward, FiniteDistribution.probability_pushforward]
  unfold FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro lr _
  have he : selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i)) =
      (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
       mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) :=
    Prod.ext (selectedQuestionTuple_left selected s.1.1 _)
      (selectedQuestionTuple_right selected s.1.1 _)
  rw [he]
  cases hevent : event (mergeCoordinates selected (fun i => (s.1.1 i).1) lr.1,
    mergeCoordinates selected (fun i => (s.1.1 i).2) lr.2) <;> simp [hevent]

theorem selected_completion_event_row (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j)
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (∑ xy : Q₁ × Q₂, (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
      ((selectedFullLeftCompletion G strategy selected j (xy.1,s)).product
        (selectedFullRightCompletion G strategy selected j (xy.2,s))).probability event) =
    ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
      partialRevealWeight G.questions j s.2 u *
        selectedOutsideLikelihood G strategy selected s.1 u *
          (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
  classical
  have hpoint (xy : Q₁ × Q₂)
      (lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂)) :
      (selectedCommonLaw G strategy selected positive j).weight (s,xy) *
        ((selectedLeftCompletion G strategy selected j s xy.1).product
          (selectedRightCompletion G strategy selected j s xy.2)).weight lr =
      if (lr.1 j,lr.2 j) = xy then
        partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
          selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0 :=
    selected_completion_row_recombine G strategy selected positive j s xy lr.1 lr.2
  simp_rw [selected_full_completion_probability, Finset.mul_sum, ← mul_assoc,
    hpoint]
  have hsum (xy : Q₁ × Q₂) :
      (∑ lr : ({i : Fin n // i ∉ selected} → Q₁) × ({i : Fin n // i ∉ selected} → Q₂),
        (if (lr.1 j,lr.2 j) = xy then
          partialRevealWeight G.questions j s.2 (fun i => (lr.1 i,lr.2 i)) *
            selectedOutsideLikelihood G strategy selected s.1 (fun i => (lr.1 i,lr.2 i)) else 0) *
          (if event (selectedQuestionTuple selected s.1.1 (fun i => (lr.1 i,lr.2 i))) then 1 else 0)) =
      ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
        (if u j = xy then partialRevealWeight G.questions j s.2 u *
          selectedOutsideLikelihood G strategy selected s.1 u else 0) *
            (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
    exact ((completionTupleEquiv (I := {i : Fin n // i ∉ selected})
      (X := Q₁) (Y := Q₂)).sum_comp _).symm
  simp_rw [hsum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_mul]
  simp

theorem selectedFullCompletionMixture_probability (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected})
    (event : ((Fin n → Q₁) × (Fin n → Q₂)) → Bool) :
    (selectedFullCompletionMixture G strategy selected positive j).probability event =
      ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability event := by
  erw [FiniteDistribution.probability_condition]
  rw [selectedFullCompletionMixture, FiniteDistribution.probability_mixture]
  simp only [FiniteDistribution.transport]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ s : SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂) (A₁ := A₁) (A₂ := A₂) selected j,
        ∑ u : {i : Fin n // i ∉ selected} → Q₁ × Q₂,
          partialRevealWeight G.questions j s.2 u *
            selectedOutsideLikelihood G strategy selected s.1 u *
              (if event (selectedQuestionTuple selected s.1.1 u) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      exact selected_completion_event_row G strategy selected positive j s event
    _ = _ := selected_partial_event_total G strategy selected j event

/-- Exact equality with the actual repeated-game question law conditioned on
the selected wins, derived by summing the local completion rows. -/
theorem selectedFullCompletionMixture_eq_conditionedQuestions (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    selectedFullCompletionMixture G strategy selected positive j =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro q
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  exact selectedFullCompletionMixture_probability G strategy selected positive j _

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Actual finite shared seed laws for the bounded correlated sampler. -/

namespace UniqueGamesTheorem.Foundations.Repetition

open scoped BigOperators
open Games
noncomputable section

universe u

theorem traceSeedLaw_expectation {σ : Type*} [Fintype σ]
    (μ : FiniteDistribution σ) (n : Nat) (f : List σ → ℝ) :
    (traceSeedLaw μ n).expectation (fun seed => f (traceList n seed)) =
      CorrelatedSampling.traceAverage μ.weight n f := by
  induction n generalizing f with
  | zero => simp [traceSeedLaw, traceList, FiniteDistribution.expectation,
      CorrelatedSampling.traceAverage]
  | succ n ih =>
      change (μ.product (traceSeedLaw μ n)).expectation
        (fun seed => f (seed.1 :: traceList n seed.2)) = _
      rw [FiniteDistribution.expectation_product]
      simp only [CorrelatedSampling.traceAverage, FiniteDistribution.expectation]
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact ih (fun xs => f (s :: xs))

theorem sharedOutputLaw_weight {X Y S Seed : Type*}
    [Fintype X] [Fintype Y] [Fintype S] [Fintype Seed] [DecidableEq S]
    (μ : FiniteDistribution (X × Y)) (seedLaw : FiniteDistribution Seed)
    (left : Seed → X → S) (right : Seed → Y → S) (x : X) (y : Y) (a b : S) :
    (sharedOutputLaw μ seedLaw left right).weight ((x,y),a,b) =
      μ.weight (x,y) * seedLaw.expectation
        (fun seed => if left seed x = a ∧ right seed y = b then 1 else 0) := by
  classical
  simp only [sharedOutputLaw, FiniteDistribution.pushforward,
    FiniteDistribution.product, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [and_assoc, ite_and]
  simp [FiniteDistribution.expectation, Finset.mul_sum, mul_ite]

section Rectangle

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

omit [Nonempty S] [DecidableEq S] in
theorem probability_weight_le_one (μ : FiniteDistribution S) (s : S) : μ.weight s ≤ 1 := by
  calc
    μ.weight s ≤ ∑ t, μ.weight t :=
      Finset.single_le_sum (fun t _ => μ.nonnegative t) (Finset.mem_univ s)
    _ = 1 := μ.normalized

/-- The per-label estimate concerns the actual finite game-law
sampler with a shared seed independent of the input questions. -/
theorem samplerOutputLaw_diagonal (thresholds : List ℝ)
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (hL : ∀ x s, (L x).weight s ∈ thresholds)
    (hR : ∀ y s, (R y).weight s ∈ thresholds)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - eventMass (rectangleWeight thresholds)
          (fun s => !(rectangleAccept thresholds (L x).weight s ||
            rectangleAccept thresholds (R y).weight s)) ^ n) ≤
      (samplerOutputLaw thresholds μ L R fallback n).weight ((x,y),a,a) := by
  have h := rectangle_label_diagonal_bound thresholds (L x).weight (R y).weight
    fallback a (hL x) (hR y) (L x).nonnegative (R y).nonnegative
    (probability_weight_le_one (L x)) (probability_weight_le_one (R y))
    (L x).normalized (R y).normalized n
  rw [samplerOutputLaw, sharedOutputLaw_weight]
  have he : (traceSeedLaw (rectangleDistribution (α := S) thresholds) n).expectation
      (fun seed => if samplerLocal thresholds L fallback n seed x = a ∧
        samplerLocal thresholds R fallback n seed y = a then 1 else 0) =
      traceAverage (rectangleWeight thresholds) n
        (localDiagonal (rectangleAccept thresholds (L x).weight)
          (rectangleAccept thresholds (R y).weight) Prod.fst fallback a) := by
    exact traceSeedLaw_expectation (rectangleDistribution (α := S) thresholds) n
      (localDiagonal (rectangleAccept thresholds (L x).weight)
        (rectangleAccept thresholds (R y).weight) Prod.fst fallback a)
  rw [he]
  simp only [Information.totalVariation, CorrelatedSampling.totalVariation] at h ⊢
  simpa only [mul_div_assoc, mul_assoc] using
    mul_le_mul_of_nonneg_left h (μ.nonnegative (x,y))

theorem samplerOutputLaw_uniform_diagonal
    (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) (x : X) (y : Y) (a : S) :
    μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
        (1 + Information.totalVariation (L x).weight (R y).weight) *
        (1 - uniformRejectionRate S ^ n) ≤
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight ((x,y),a,a) := by
  have hp := pow_le_pow_left₀ (sharedProfileReject_nonnegative L R x y)
    (sharedProfile_reject_le_rate L R x y) n
  have hco : 0 ≤ μ.weight (x,y) * min ((L x).weight a) ((R y).weight a) /
      (1 + Information.totalVariation (L x).weight (R y).weight) :=
    div_nonneg (mul_nonneg (μ.nonnegative (x,y))
      (le_min ((L x).nonnegative a) ((R y).nonnegative a)))
      (by linarith [Information.totalVariation_nonneg (L x).weight (R y).weight])
  have h := samplerOutputLaw_diagonal (sharedProfileThresholds L R) μ L R
    (left_mem_sharedProfileThresholds L R) (right_mem_sharedProfileThresholds L R)
    fallback n x y a
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp 1) hco).trans h

/-- Actual finite shared sampler approximates any prescribed diagonal law.
Its error is derived from the two actual conditional profiles and its uniform
finite exhaustion probability. -/
theorem samplerOutputLaw_totalVariation
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (n : Nat) :
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) +
      uniformRejectionRate S ^ n := by
  apply diagonal_sampler_totalVariation_le p.weight μ.weight
    (fun xy => (L xy.1).weight) (fun xy => (R xy.2).weight) _
    (Information.gameLaw_isProbability p) (Information.gameLaw_isProbability μ)
    (fun xy => Information.gameLaw_isProbability (L xy.1))
    (fun xy => Information.gameLaw_isProbability (R xy.2))
    (Information.gameLaw_isProbability _)
    (pow_nonneg (uniformRejectionRate_nonnegative S) n)
  · exact pow_le_one₀ (uniformRejectionRate_nonnegative S)
      (uniformRejectionRate_lt_one S).le
  · intro xy a
    exact samplerOutputLaw_uniform_diagonal μ L R fallback n xy.1 xy.2 a

theorem samplerOutputLaw_arbitrarily_close
    (p : FiniteDistribution ((X × Y) × S)) (μ : FiniteDistribution (X × Y))
    (L : X → FiniteDistribution S) (R : Y → FiniteDistribution S)
    (fallback : S) (η : ℝ) (hη : 0 < η) : ∃ n : Nat,
    Information.totalVariation
      (samplerOutputLaw (sharedProfileThresholds L R) μ L R fallback n).weight
      (diagonalWeights p.weight) ≤
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (L z.1.1).weight z.2) +
      2 * Information.totalVariation p.weight (fun z => μ.weight z.1 * (R z.1.2).weight z.2) + η := by
  obtain ⟨n,hn⟩ := exists_uniformRejectionRate_pow_lt S η hη
  exact ⟨n, (samplerOutputLaw_totalVariation p μ L R fallback n).trans
    (by linarith)⟩

end Rectangle

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_CompletedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OccurrenceGame.toGame_success _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.restrict_extend _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.success_restrict _root_.OAI.PerfectCompleteness.OccurrenceVertexEmbedding.wins_restrict _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.PerfectCompleteness.SourceGame.questionGame_success _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite local completion after correlated sampling

One independent seed contains the original shared seed and two full response
tables. Its local reads give exactly the mixture of the requested completion
kernels. Applying those kernels contracts total variation. On a diagonal
target the same construction uses one common selected label.
-/

namespace UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight c)

theorem product_pushforward_eq_mixture_right (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (f : A × B → C) :
    (μ.product ν).pushforward f =
      ν.mixture (fun b => μ.pushforward (fun a => f (a, b))) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f (a, b) = c <;> simp [h, mul_comm]

theorem product_product_pushforward_eq_mixture (μ : FiniteDistribution A)
    (ν : FiniteDistribution B) (κ : FiniteDistribution C) (f : A → B → C → D) :
    (μ.product (ν.product κ)).pushforward (fun z => f z.1 z.2.1 z.2.2) =
      (μ.product ν).mixture
        (fun z => κ.pushforward (fun c => f z.1 z.2 c)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro d
  simp only [FiniteDistribution.pushforward, FiniteDistribution.product,
    FiniteDistribution.mixture, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem mixture_totalVariation_le (μ ν : FiniteDistribution A)
    (K : A → FiniteDistribution B) :
    (μ.mixture K).totalVariation (ν.mixture K) ≤ μ.totalVariation ν := by
  simpa only [FiniteDistribution.totalVariation, FiniteDistribution.mixture,
    Information.totalVariation, kernelPushforward] using
      totalVariation_kernelPushforward_le μ.weight ν.weight
        (fun a => (K a).weight) (fun a => Information.gameLaw_isProbability (K a))

end DistributionIdentities

section Diagonal

variable {Z S : Type*} [Fintype Z] [Fintype S]

theorem diagonalLaw_eq_pushforward (σ : FiniteDistribution (Z × S)) :
    diagonalLaw σ = σ.pushforward (fun z => (z.1, z.2, z.2)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨z, a, b⟩
  change diagonalWeights σ.weight (z, a, b) =
    (σ.pushforward (fun t => (t.1, t.2, t.2))).weight (z, a, b)
  simp only [diagonalWeights, FiniteDistribution.pushforward,
    Fintype.sum_prod_type, Prod.mk.injEq]
  by_cases hab : a = b
  · subst b
    simp [ite_and]
  · simp [hab, ite_and]

theorem diagonalLaw_mixture {T : Type*} [Fintype T]
    (σ : FiniteDistribution (Z × S)) (K : Z × S × S → FiniteDistribution T) :
    (diagonalLaw σ).mixture K = σ.mixture (fun z => K (z.1, z.2, z.2)) := by
  rw [diagonalLaw_eq_pushforward, mixture_pushforward_base]

end Diagonal

section Completion

variable {X Y S Γ U V : Type*}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ] [Fintype U] [Fintype V]
  [DecidableEq X] [DecidableEq Y] [DecidableEq S]

theorem outputLaw_eq_product_pushforward
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (μ.product (seedLaw γ L R)).pushforward
        (fun z => (left sL z.2 z.1.1, right sR z.2 z.1.2)) := by
  exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
    (fun z : (X × Y) × Seed Γ X Y S U V =>
      (left sL z.2 z.1.1, right sR z.2 z.1.2))).symm

/-- The completion mixture is derived from actual local table reads. -/
theorem outputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    outputLaw μ γ sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    outputLaw μ γ sL sR L R =
        (μ.product γ).mixture (fun z =>
          (KernelSampling.seedLaw L R).pushforward (fun table =>
            (KernelSampling.readLeft table (z.1.1, sL z.2 z.1.1),
             KernelSampling.readRight table (z.1.2, sR z.2 z.1.2)))) := by
      rw [outputLaw_eq_product_pushforward]
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.readLeft table (q.1, sL seed q.1),
           KernelSampling.readRight table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.read_joint_pushforward L R
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

omit [DecidableEq X] [DecidableEq Y] [DecidableEq S] in
/-- The diagonal target uses the same selected label for both completion rows. -/
theorem diagonalLaw_completion_mixture
    (σ : FiniteDistribution ((X × Y) × S))
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V) :
    (diagonalLaw σ).mixture (completionKernel L R) =
      σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2))) := by
  exact diagonalLaw_mixture σ (completionKernel L R)

/-- Completing local outputs incurs no additional total-variation loss. -/
theorem outputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution U) (R : Y × S → FiniteDistribution V)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (outputLaw μ γ sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [outputLaw_eq_mixture, ← diagonalLaw_completion_mixture σ L R]
  exact mixture_totalVariation_le _ _ (completionKernel L R)

end Completion

section CoordinateCompletion

variable {I X Y S Γ : Type*}
  [Fintype I] [Fintype X] [Fintype Y] [Fintype S] [Fintype Γ]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y] [DecidableEq S]

/-- Supported coordinate repair preserves the exact completion mixture. -/
theorem coordinateOutputLaw_eq_mixture
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R =
      (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
  calc
    coordinateOutputLaw μ γ j sL sR L R =
        (μ.product (seedLaw γ L R)).pushforward
          (fun z => (coordinateLeft j sL z.2 z.1.1,
            coordinateRight j sR z.2 z.1.2)) := by
      exact (product_pushforward_eq_mixture_right μ (seedLaw γ L R)
        (fun z : (X × Y) × Seed Γ X Y S (I → X) (I → Y) =>
          (coordinateLeft j sL z.2 z.1.1, coordinateRight j sR z.2 z.1.2))).symm
    _ = (μ.product γ).mixture (fun z =>
        (KernelSampling.seedLaw L R).pushforward (fun table =>
          (KernelSampling.completedLeft j table (z.1.1, sL z.2 z.1.1),
           KernelSampling.completedRight j table (z.1.2, sR z.2 z.1.2)))) := by
      exact product_product_pushforward_eq_mixture μ γ (KernelSampling.seedLaw L R)
        (fun q seed table =>
          (KernelSampling.completedLeft j table (q.1, sL seed q.1),
           KernelSampling.completedRight j table (q.2, sR seed q.2)))
    _ = (μ.product γ).mixture (fun z =>
        completionKernel L R (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) := by
      apply congrArg ((μ.product γ).mixture)
      funext z
      exact KernelSampling.completed_joint_pushforward L R j hL hR
        (z.1.1, sL z.2 z.1.1) (z.1.2, sR z.2 z.1.2)
    _ = (sharedOutputLaw μ γ sL sR).mixture (completionKernel L R) := by
      exact (mixture_pushforward_base (μ.product γ)
        (fun z => (z.1, sL z.2 z.1.1, sR z.2 z.1.2)) (completionKernel L R)).symm

theorem coordinateOutputLaw_eq_outputLaw
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1) :
    coordinateOutputLaw μ γ j sL sR L R = outputLaw μ γ sL sR L R := by
  rw [coordinateOutputLaw_eq_mixture μ γ j sL sR L R hL hR, outputLaw_eq_mixture]

theorem coordinateOutputLaw_totalVariation_le
    (μ : FiniteDistribution (X × Y)) (γ : FiniteDistribution Γ)
    (j : I) (sL : Γ → X → S) (sR : Γ → Y → S)
    (L : X × S → FiniteDistribution (I → X))
    (R : Y × S → FiniteDistribution (I → Y))
    (hL : ∀ q xs, (L q).weight xs ≠ 0 → xs j = q.1)
    (hR : ∀ q ys, (R q).weight ys ≠ 0 → ys j = q.1)
    (σ : FiniteDistribution ((X × Y) × S)) :
    (coordinateOutputLaw μ γ j sL sR L R).totalVariation
        (σ.mixture (fun z => (L (z.1.1, z.2)).product (R (z.1.2, z.2)))) ≤
      (sharedOutputLaw μ γ sL sR).totalVariation (diagonalLaw σ) := by
  rw [coordinateOutputLaw_eq_outputLaw μ γ j sL sR L R hL hR]
  exact outputLaw_totalVariation_le μ γ sL sR L R σ

end CoordinateCompletion

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

section

/-! An explicit finite shared sampler followed by supported local completion
gives the coordinate success bound. No embedding-existence premise remains. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games CorrelatedSampling
noncomputable section
variable {Q₁ Q₂ A₁ A₂ S : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype S]
  [Nonempty A₁] [Nonempty A₂] [Nonempty S]
  [DecidableEq Q₁] [DecidableEq Q₂] [DecidableEq S] {n : Nat}

theorem coordinate_probability_le_value_of_local_completion
    (G : Game Q₁ Q₂ A₁ A₂) (j : Fin n)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (σ : FiniteDistribution ((Q₁ × Q₂) × S))
    (profileL : Q₁ → FiniteDistribution S) (profileR : Q₂ → FiniteDistribution S)
    (completionL : Q₁ × S → FiniteDistribution (Fin n → Q₁))
    (completionR : Q₂ × S → FiniteDistribution (Fin n → Q₂))
    (supportL : ∀ q xs, (completionL q).weight xs ≠ 0 → xs j = q.1)
    (supportR : ∀ q ys, (completionR q).weight ys ≠ 0 → ys j = q.1)
    (fallback : S) :
    (σ.mixture (fun z => (completionL (z.1.1,z.2)).product
      (completionR (z.1.2,z.2)))).probability (G.coordinateWin strategy j) ≤
      G.value +
        (2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
         2 * Information.totalVariation σ.weight
          (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)) := by
  let targetLaw := σ.mixture (fun z => (completionL (z.1.1,z.2)).product (completionR (z.1.2,z.2)))
  let δ := 2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileL z.1.1).weight z.2) +
    2 * Information.totalVariation σ.weight
      (fun z => G.questions.weight z.1 * (profileR z.1.2).weight z.2)
  change targetLaw.probability (G.coordinateWin strategy j) ≤ G.value + δ
  by_contra h
  have gap : 0 < targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ) :=
    sub_pos.mpr (lt_of_not_ge h)
  let η := (targetLaw.probability (G.coordinateWin strategy j) - (G.value + δ)) / 2
  have hη : 0 < η := by dsimp [η] <;> linarith
  obtain ⟨N,hN⟩ := samplerOutputLaw_arbitrarily_close σ G.questions profileL profileR fallback η hη
  let thresholds := sharedProfileThresholds profileL profileR
  let γ := traceSeedLaw (rectangleDistribution (α := S) thresholds) N
  let sL := samplerLocal thresholds profileL fallback N
  let sR := samplerLocal thresholds profileR fallback N
  have hvariation := CompletedSampling.coordinateOutputLaw_totalVariation_le
    G.questions γ j sL sR completionL completionR supportL supportR σ
  have hclose : (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw ≤ δ + η :=
    hvariation.trans hN
  have hsuccess := G.coordinate_probability_le_value_add_embedding_distance j targetLaw
    (CompletedSampling.seedLaw γ completionL completionR)
    (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)
    (CompletedSampling.coordinateLeft_preserves j sL)
    (CompletedSampling.coordinateRight_preserves j sR) strategy
  have hsym : targetLaw.totalVariation
      (G.localEmbeddingLaw (CompletedSampling.seedLaw γ completionL completionR)
        (CompletedSampling.coordinateLeft j sL) (CompletedSampling.coordinateRight j sR)) =
      (CompletedSampling.coordinateOutputLaw G.questions γ j sL sR completionL completionR).totalVariation targetLaw := by
    unfold FiniteDistribution.totalVariation
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    exact abs_sub_comm _ _
  rw [hsym] at hsuccess
  dsimp [η] at hclose
  linarith

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! The two actual conditional common-data profiles used by the shared
sampler, with explicit normalized default laws on all null inputs. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games Information
noncomputable section

theorem finiteDistribution_nonempty {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    Nonempty A := by
  have hsum : (∑ a, μ.weight a) ≠ 0 := by rw [μ.normalized]; norm_num
  obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨a⟩

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selectedSamplingTarget_left_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedLeftProfile G strategy selected positive j z.1.1).weight z.2) =
      selectedLeftProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedLeftProfile G strategy selected positive j z.2.1).weight z.1)

theorem selectedSamplingTarget_right_error (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    totalVariation (selectedSamplingTarget G strategy selected positive j).weight
      (fun z => G.questions.weight z.1 * (selectedRightProfile G strategy selected positive j z.1.2).weight z.2) =
      selectedRightProfileError G strategy selected positive j := by
  exact totalVariation_comp_equiv
    (Equiv.prodComm (Q₁ × Q₂) (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j))
    (selectedCommonLaw G strategy selected positive j).weight
    (fun z => G.questions.weight z.2 * (selectedRightProfile G strategy selected positive j z.2.2).weight z.1)

end
end UniqueGamesTheorem.Foundations.Repetition

end

section

/-! Quantitative parallel repetition for actual finite two-player games.
The coordinate bound is derived from the explicitly conditioned question law,
finite reveal variables, information estimates, shared rejection sampler,
and normalized local completions. The scalar recurrence is then applied to
the actual repeated strategy's success probability. -/
namespace UniqueGamesTheorem.Foundations.Repetition
open scoped BigOperators
open Games
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

theorem selected_coordinate_probability_le_value_add_error_oai
    (G : Game Q₁ Q₂ A₁ A₂)
    (strategy : Strategy (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂))
    (selected : Finset (Fin n)) (positive : 0 < G.selectedSuccess strategy selected)
    (j : {i : Fin n // i ∉ selected}) :
    ((G.repetition n).questions.condition (G.selectedWins strategy selected) positive).probability
      (G.coordinateWin strategy j.1) ≤
        G.value + selectedEmbeddingError G strategy selected positive j := by
  classical
  let : Nonempty (SelectedCommonData (Q₁ := Q₁) (Q₂ := Q₂)
      (A₁ := A₁) (A₂ := A₂) selected j) :=
    finiteDistribution_nonempty (selectedProfileFallback G strategy selected positive j)
  have h := coordinate_probability_le_value_of_local_completion G j.1 strategy
    (selectedSamplingTarget G strategy selected positive j)
    (selectedLeftProfile G strategy selected positive j)
    (selectedRightProfile G strategy selected positive j)
    (selectedFullLeftCompletion G strategy selected j)
    (selectedFullRightCompletion G strategy selected j)
    (selectedFullLeftCompletion_support G strategy selected j)
    (selectedFullRightCompletion_support G strategy selected j)
    (Classical.choice inferInstance)
  have htarget : (selectedSamplingTarget G strategy selected positive j).mixture
      (fun z => (selectedFullLeftCompletion G strategy selected j (z.1.1,z.2)).product
        (selectedFullRightCompletion G strategy selected j (z.1.2,z.2))) =
      (G.repetition n).questions.condition (G.selectedWins strategy selected) positive :=
    selectedFullCompletionMixture_eq_conditionedQuestions G strategy selected positive j
  rw [htarget, selectedSamplingTarget_left_error, selectedSamplingTarget_right_error] at h
  exact h

end
end UniqueGamesTheorem.Foundations.Repetition

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error_oai.{u_1, u_2, u_3, u_4} := @OAI.UniqueGamesTheorem.Foundations.Repetition.selected_coordinate_probability_le_value_add_error_oai.{u_1, u_2, u_3, u_4}
