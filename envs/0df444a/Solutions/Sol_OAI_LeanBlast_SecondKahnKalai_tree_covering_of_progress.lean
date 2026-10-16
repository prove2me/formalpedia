-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.tree_covering_of_progress
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:14:45.679194+00:00
-- url     : https://prove2.me/submissions/a83390fe-49a4-4760-9462-b8a37c2f58fe

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean:L359-L410
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.tree_covering_of_progress. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_adaptive_rank_completion
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_mono_parameter
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliProbability_subset
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_iid_bernoulli_union_expectation

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_le_one (μ : FiniteLaw Ω) (P : Ω → Prop) : μ.prob P ≤ 1 := by
  simpa using μ.prob_mono (Q := fun _ => True) (fun _ _ => trivial)

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliProbability_eq_expectation (p : ℝ) (P : Finset X → Prop) :
    bernoulliProbability p P = bernoulliExpectation p (fun W => if P W then 1 else 0) := by
  classical
  simp [bernoulliProbability, bernoulliExpectation, mul_ite]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliUnion ----
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem iid_bernoulli_union_probability (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (P : Finset X → Prop) :
    ((bernoulliLaw p hp0 hp1).iid n).prob (fun draws => P (Finset.univ.biUnion draws)) =
      bernoulliProbability (1 - (1 - p) ^ n) P := by
  rw [FiniteLaw.prob_eq_expectation, bernoulliProbability_eq_expectation]
  exact iid_bernoulli_union_expectation p hp0 hp1 n (fun W => if P W then 1 else 0)

theorem bernoulli_union_parameter_mem {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    0 ≤ 1 - (1 - p) ^ n ∧ 1 - (1 - p) ^ n ≤ 1 := by
  have hpow0 : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp1) _
  have hpow1 : (1 - p) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)
  constructor <;> linarith

theorem bernoulli_union_parameter_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ (n : ℝ) * p := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow1 : (1 - p) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)
      have hmul := mul_le_mul_of_nonneg_left hpow1 hp0
      rw [pow_succ, Nat.cast_succ]
      nlinarith

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliMonotonicity ----
namespace OAI

/-!
# Monotonicity of finite Bernoulli probabilities

For `p ≤ q`, adjoin an independent Bernoulli set to a Bernoulli-`p` set.
The resulting union has parameter `q` and contains the first set. This gives
expectation and event monotonicity, including both endpoints of `[0, 1]`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Inclusion-monotone events become more likely as the Bernoulli parameter
increases. The proof couples actual independent finite Bernoulli sets. -/
theorem bernoulliProbability_mono_parameter {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) (P : Finset X → Prop)
    (hP : ∀ U V, U ⊆ V → P U → P V) :
    bernoulliProbability p P ≤ bernoulliProbability q P := by
  rw [bernoulliProbability_eq_expectation, bernoulliProbability_eq_expectation]
  apply bernoulliExpectation_mono_parameter hp0 hpq hq1
  intro U V hUV
  by_cases hu : P U
  · simp [hu, hP U V hUV hu]
  · by_cases hv : P V <;> simp [hu, hv]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.ProbabilityTreePaths ----
namespace OAI

/-! Full-path interpretation of supports and structural disjointness. -/

noncomputable section

namespace LeanBlast.SecondKahnKalai.ProbabilityTree

variable {X : Type} [DecidableEq X]

theorem coveredBy_mono {d : ℕ} {T : ProbabilityTree X d} {W V : Finset X}
    (h : T.CoveredBy W) (hWV : W ⊆ V) : T.CoveredBy V := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, hp.trans hWV⟩

theorem coveredBy_univ [Fintype X] {d : ℕ} (T : ProbabilityTree X d) :
    T.CoveredBy Finset.univ :=
  ⟨choosePath T, Finset.subset_univ _⟩

end LeanBlast.SecondKahnKalai.ProbabilityTree

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.CapacityIteration ----
-- Lean 4.34 name of Finset.prod_le_prod_of_subset_of_le_one (ordered-semiring version) in Mathlib 0df444a.
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Capacities and finite inflation products

The capacity after `t` successful reductions is natural-number division by
`2^t`. All product estimates below are finite; no infinite product is used.
-/

noncomputable section

open Finset Set

namespace LeanBlast.SecondKahnKalai

theorem successesNeeded_le_logb (l : ℕ) :
    (successesNeeded l : ℝ) ≤ 1 + Real.logb 2 (l : ℝ) := by
  have h := Real.log2_le_logb l
  simp only [successesNeeded, Nat.cast_add, Nat.cast_one]
  linarith

theorem capacity_logb_nonneg {l : ℕ} (hl : 1 ≤ l) :
    0 ≤ Real.logb 2 (l : ℝ) :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast hl)

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.TreeCovering ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# Covering a probability tree by iterative reductions

Recovery keeps the original and retained path histories distinct, even when
their labels agree. All draws are retained in the accumulating union.
-/

noncomputable section
open Classical

namespace LeanBlast.SecondKahnKalai

theorem sampling_budget_le {σ : ℝ} (hσ : 0 ≤ σ) (L : ℕ) :
    ((4 * successesNeeded L : ℕ) : ℝ) * (Real.exp 50 * (4 * σ)) ≤
      16 * Real.exp 50 * σ * (1 + Real.logb 2 (L : ℝ)) := by
  calc
    _ = (16 * Real.exp 50 * σ) * (successesNeeded L : ℝ) := by push_cast; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (successesNeeded_le_logb L) (by positivity)

namespace ProbabilityTree

variable {X : Type} [DecidableEq X]

/-- When no levels remain, recovery is already a covering certificate. -/
theorem Recovers.coveredBy_of_depth_zero {d : ℕ} {T : ProbabilityTree X d}
    {S : ProbabilityTree X 0} {W : Finset X} (h : Recovers T S W) : T.CoveredBy W := by
  cases S
  obtain ⟨p, hp⟩ := h PUnit.unit
  exact ⟨p, by simpa only [pathUnion, Finset.union_empty] using hp⟩

theorem Recovers.coveredBy_of_depth_eq_zero {d e : ℕ} {T : ProbabilityTree X d}
    {S : ProbabilityTree X e} {W : Finset X} (h : Recovers T S W) (he : e = 0) :
    T.CoveredBy W := by
  subst e
  exact h.coveredBy_of_depth_zero

theorem coveredBy_probability_one [Fintype X] {d : ℕ} (T : ProbabilityTree X d) :
    bernoulliProbability 1 T.CoveredBy = 1 := by
  apply le_antisymm
  · exact (bernoulliLaw 1 (by norm_num) le_rfl).prob_le_one T.CoveredBy
  · have h := (bernoulliLaw (X := X) 1 (by norm_num) le_rfl).prob_mono
      (P := fun W => Finset.univ ⊆ W) (Q := T.CoveredBy)
      (fun _ hW => coveredBy_mono (coveredBy_univ T) hW)
    change bernoulliProbability 1 (fun W => Finset.univ ⊆ W) ≤
      bernoulliProbability 1 T.CoveredBy at h
    simpa only [bernoulliProbability_subset, one_pow] using h

namespace CoverState

variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

theorem coveredBy_of_rank_zero (state : CoverState original σ) (h : state.rank = 0) :
    original.CoveredBy state.seen :=
  state.recovery.coveredBy_of_depth_eq_zero ((rank_eq_zero_iff state).mp h)

theorem step_seen (state : CoverState original σ) (W : Finset X) :
    (state.step W).seen = state.seen ∪ W := by
  unfold step
  split_ifs with h
  · exact (Classical.choose_spec h).2
  · rfl

theorem step_rank_le (state : CoverState original σ) (W : Finset X) :
    (state.step W).rank ≤ state.rank := by
  unfold step
  split_ifs with h
  · exact (Classical.choose_spec h).1.le
  · exact le_rfl

theorem step_rank_lt_of_exists (state : CoverState original σ) (W : Finset X)
    (h : ∃ next, state.Advances W next) : (state.step W).rank < state.rank := by
  unfold step
  rw [dite_eq_left h]
  exact (Classical.choose_spec h).1

theorem biUnion_fin_succ {n : ℕ} (draws : Fin (n + 1) → Finset X) :
    Finset.univ.biUnion draws = draws 0 ∪ Finset.univ.biUnion (fun i : Fin n => draws i.succ) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    refine Fin.cases (fun hx => Or.inl hx) (fun j hx => Or.inr ⟨j, hx⟩) i hi
  · rintro (h | ⟨i, hi⟩)
    · exact ⟨0, h⟩
    · exact ⟨i.succ, hi⟩

/-- The recorded set is exactly the union of all draws, including failures. -/
theorem run_seen (n : ℕ) (state : CoverState original σ) (draws : Fin n → Finset X) :
    (adaptiveRun step n state draws).seen = state.seen ∪ Finset.univ.biUnion draws := by
  induction n generalizing state with
  | zero => simp [adaptiveRun]
  | succ n ih =>
      rw [adaptiveRun, ih, step_seen, biUnion_fin_succ, Finset.union_assoc]

/-- The finite adaptive theorem transfers actual strict advances to covering.
The good-tree probability estimate supplies the premise in the final theorem. -/
theorem prob_covered_of_advance_probability [Fintype X] (μ : FiniteLaw (Finset X))
    (hprogress : ∀ state : CoverState original σ, state.rank ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun W => ∃ next, state.Advances W next))
    (s : ℕ) (state : CoverState original σ) (hrank : state.rank ≤ s) :
    (2 / 3 : ℝ) ≤ (μ.iid (4 * s)).prob
      (fun draws => original.CoveredBy (state.seen ∪ Finset.univ.biUnion draws)) := by
  have hp : ∀ st : CoverState original σ, st.rank ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun W => (st.step W).rank < st.rank) := by
    intro st hst
    exact (hprogress st hst).trans (μ.prob_mono fun W hW => st.step_rank_lt_of_exists W hW)
  have hcomplete := adaptive_rank_completion μ rank step step_rank_le hp s state hrank
  apply hcomplete.trans
  apply (μ.iid (4 * s)).prob_mono
  intro draws hdraws
  have hcover := (adaptiveRun step (4 * s) state draws).coveredBy_of_rank_zero hdraws
  rwa [run_seen] at hcover

end CoverState

end ProbabilityTree

/-- The finite random experiment and final parameter comparison. The next
theorem supplies this private lemma's progress estimate from actual reduction. -/
private theorem tree_covering_of_progress {X : Type} [Fintype X] [DecidableEq X]
    {k : ℕ} (T : ProbabilityTree X k) (hk : 0 < k) (hdis : T.IsDisjoint)
    (m : ℕ → ℕ) (hcap : T.HasCapacities m) (hpos : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1))
    (σ : ℝ) (hσ : 0 < σ) (hspread : T.HasSpread (fun _ => σ))
    (hprogress : Real.exp 50 * (4 * σ) < 1 →
      ∀ state : ProbabilityTree.CoverState T σ, state.rank ≠ 0 →
        (3 / 4 : ℝ) ≤ bernoulliProbability (Real.exp 50 * (4 * σ))
          (fun W => ∃ next, state.Advances W next)) :
    (2 / 3 : ℝ) ≤ bernoulliProbability
      (min 1 (16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ)))) T.CoveredBy := by
  let B := 16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ))
  change (2 / 3 : ℝ) ≤ bernoulliProbability (min 1 B) T.CoveredBy
  by_cases hB : 1 ≤ B
  · rw [min_eq_left hB, ProbabilityTree.coveredBy_probability_one]
    norm_num
  have hB1 : B < 1 := lt_of_not_ge hB
  let p := Real.exp 50 * (4 * σ)
  have hp : 0 < p := by dsimp [p]; positivity
  have hlog : 0 ≤ Real.logb 2 (m (k - 1) : ℝ) :=
    capacity_logb_nonneg (hpos (k - 1) (by omega))
  have hBp : 4 * p ≤ B := by
    calc
      4 * p = (16 * Real.exp 50 * σ) * 1 := by dsimp [p]; ring
      _ ≤ B := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤
        1 + Real.logb 2 (m (k - 1) : ℝ)) (by positivity)
  have hp1 : p < 1 := by linarith
  let μ := bernoulliLaw (X := X) p hp.le hp1.le
  let state := ProbabilityTree.CoverState.initial T σ m hσ hdis hcap hspread hpos hgrowth
  let s := successesNeeded (m (k - 1))
  have hrank : state.rank ≤ s := by
    change (if k = 0 then 0 else successesNeeded (m (k - 1))) ≤ s
    rw [ite_eq_right (Nat.ne_of_gt hk)]
  have hprog : ∀ st : ProbabilityTree.CoverState T σ, st.rank ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun W => ∃ next, st.Advances W next) :=
    fun st hst => hprogress hp1 st hst
  have hc := ProbabilityTree.CoverState.prob_covered_of_advance_probability μ hprog s state hrank
  have hseen : state.seen = ∅ := rfl
  simp only [hseen, Finset.empty_union] at hc
  change (2 / 3 : ℝ) ≤ ((bernoulliLaw p hp.le hp1.le).iid (4 * s)).prob
    (fun draws => T.CoveredBy (Finset.univ.biUnion draws)) at hc
  rw [iid_bernoulli_union_probability] at hc
  have hq0 := (bernoulli_union_parameter_mem hp.le hp1.le (4 * s)).1
  have hqB : 1 - (1 - p) ^ (4 * s) ≤ B :=
    (bernoulli_union_parameter_le hp.le hp1.le (4 * s)).trans
      (sampling_budget_le hσ.le (m (k - 1)))
  have hmono := bernoulliProbability_mono_parameter hq0 hqB hB1.le T.CoveredBy
    (fun _ _ hUV hU => ProbabilityTree.coveredBy_mono hU hUV)
  rw [min_eq_right hB1.le]
  exact hc.trans hmono

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Classical


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.tree_covering_of_progress := @_root_.OAI.LeanBlast.SecondKahnKalai.tree_covering_of_progress
