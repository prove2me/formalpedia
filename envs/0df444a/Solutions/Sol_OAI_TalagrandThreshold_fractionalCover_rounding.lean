-- Prove2me | solution 1 for OAI.TalagrandThreshold.fractionalCover_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:17:23.078603+00:00
-- url     : https://prove2.me/submissions/77de5be1-cb5c-4f37-bb10-bde852ebd40c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/RoundingMain.lean:L47-L93
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.fractionalCover_rounding. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorGlobalCost
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMain
import Theorems.Thm_OAI_TalagrandThreshold_Selector_half_bad_probability_le_selected_cost
import Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_total_cost_lt_one_twentieth
import Theorems.Thm_OAI_TalagrandThreshold_Selector_sum_color_tail_indicators
import Theorems.Thm_OAI_TalagrandThreshold_color_mean_le
import Theorems.Thm_OAI_TalagrandThreshold_expectation_productScore_le
import Theorems.Thm_OAI_TalagrandThreshold_productScore_lower_of_mean

-- ---- from OAI.Combinatorics.ExpectationThreshold.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
theorem small_empty (p : ℝ) : Small p (∅ : Family α) := by
  refine ⟨∅, covers_empty _, ?_⟩
  simp

omit [Fintype α] [DecidableEq α] in
theorem members_nonempty {F : Family α} (hF : (∅ : Finset α) ∉ F)
    {H : Finset α} (hH : H ∈ F) : H.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  exact hF (he ▸ hH)

end
end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityFinite ----
namespace OAI

/-!
# Finite probability laws

Probabilities and expectations are finite real sums. Independent samples,
product laws, and uniform laws satisfy the usual elementary inequalities.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandThreshold

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

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

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

theorem prob_ge_le_expectation_div (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expectation f / t := by
  have h := μ.prob_le_expectation (fun ω => t ≤ f ω) (fun ω => t⁻¹ * f ω)
    (fun ω => mul_nonneg (inv_nonneg.mpr ht.le) (hf ω))
    (fun ω hω => by simpa [ht.ne'] using mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr ht.le))
  rw [expectation_smul] at h
  simpa [div_eq_mul_inv, mul_comm] using h

end FiniteLaw

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingExpectation ----
namespace OAI

/-!
# The upper expectation bound for rounding

The score sums over nonempty subsets of the original ground set. Its moments
come from the actual coordinate product law. Nonemptiness saves a factor of
one fifth in the fractional-cover cost.
-/

open scoped BigOperators

namespace TalagrandThreshold

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem productScore_nonneg {g : Finset α → ℝ} {Y : α → ℝ}
    (hg : ∀ S, 0 ≤ g S) (hY : ∀ x, 0 ≤ Y x) : 0 ≤ productScore g Y := by
  exact Finset.sum_nonneg fun S _ =>
    mul_nonneg (hg S) (Finset.prod_nonneg fun x _ => hY x)

variable {Ω : Type*} [Fintype Ω]

/-- The budget one half gives the upper bound one tenth for the same score. -/
theorem expectation_productScore_le_tenth (ν : FiniteLaw Ω) (g : Finset α → ℝ)
    (Y : Ω → ℝ) {r : ℝ} (hg : ∀ S, 0 ≤ g S) (hY : ∀ ω, 0 ≤ Y ω)
    (hr : 0 ≤ r) (hmean : ν.expectation Y ≤ r / 5) (hcost : fracCost r g ≤ 1 / 2) :
    (FiniteLaw.pi (fun _ : α => ν)).expectation
        (fun ω => productScore g (fun x => Y (ω x))) ≤ 1 / 10 := by
  calc
    _ ≤ (1 / 5) * fracCost r g := expectation_productScore_le ν g Y hg hY hr hmean
    _ ≤ (1 / 5 : ℝ) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 1 / 5)
    _ = 1 / 10 := by norm_num

end
end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingProbabilityContradiction ----
namespace OAI

/-!
# The numerical contradiction used in rounding

A nonnegative score bounded below by one quarter on an event of probability
at least nine tenths has expectation at least nine fortieths.
-/

namespace TalagrandThreshold

variable {Ω : Type*} [Fintype Ω]

theorem expectation_ge_nine_fortieths (μ : FiniteLaw Ω) (P : Ω → Prop)
    (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) (hprob : (9 / 10 : ℝ) ≤ μ.prob P)
    (hlower : ∀ ω, P ω → (1 / 4 : ℝ) ≤ Z ω) :
    (9 / 40 : ℝ) ≤ μ.expectation Z := by
  have hinclusion : μ.prob P ≤ μ.prob (fun ω => (1 / 4 : ℝ) ≤ Z ω) :=
    μ.prob_mono hlower
  have hmarkov := μ.prob_ge_le_expectation_div Z hZ
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hbound : (9 / 10 : ℝ) ≤ μ.expectation Z / (1 / 4 : ℝ) :=
    hprob.trans (hinclusion.trans hmarkov)
  calc
    (9 / 40 : ℝ) = (9 / 10 : ℝ) * (1 / 4 : ℝ) := by norm_num
    _ ≤ μ.expectation Z := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 / 4)).mp hbound

theorem rounding_expectation_contradiction (μ : FiniteLaw Ω) (P : Ω → Prop)
    (Z : Ω → ℝ) (hZ : ∀ ω, 0 ≤ Z ω) (hprob : (9 / 10 : ℝ) ≤ μ.prob P)
    (hlower : ∀ ω, P ω → (1 / 4 : ℝ) ≤ Z ω)
    (hupper : μ.expectation Z ≤ (1 / 10 : ℝ)) : False := by
  have h := (expectation_ge_nine_fortieths μ P Z hZ hprob hlower).trans hupper
  exact (by norm_num : ¬ ((9 / 40 : ℝ) ≤ 1 / 10)) h

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ScaleBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-!
# The largest admissible scale

The cutoff is constructed as the first index whose next scale fails.
Its existence follows from the Archimedean property and the elementary
lower bound `scaleSum s ≥ s`. No finite search bound or computed large
power is used.
-/

namespace TalagrandThreshold

open scoped BigOperators

private theorem half_geometric_sum_identity (s : ℕ) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) + (1 / 2 : ℝ) ^ s = 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
      simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      rw [pow_succ (1 / 2 : ℝ) s]
      nlinarith

theorem half_geometric_sum_le_one (s : ℕ) :
    (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) ≤ 1 := by
  have h := half_geometric_sum_identity s
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ s := by positivity
  linarith

private theorem maxScale_eq_find {p : ℝ} (hp : 0 < p) :
    maxScale p = Nat.find (scale_next_fail_exists hp) := by
  classical
  simp only [maxScale, dite_eq_left hp]

theorem maxScale_next_fail {p : ℝ} (hp : 0 < p) :
    1 / 2 < p * scaleSum (maxScale p + 1) := by
  classical
  rw [maxScale_eq_find hp]
  exact Nat.find_spec (scale_next_fail_exists hp)

theorem maxScale_admissible {p : ℝ} (hp : 0 < p) :
    p * scaleSum (maxScale p) ≤ 1 / 2 := by
  classical
  cases hs : maxScale p with
  | zero => simp [scaleSum_zero]
  | succ s =>
      have hslt : s < Nat.find (scale_next_fail_exists hp) := by
        rw [← maxScale_eq_find hp, hs]
        exact Nat.lt_succ_self s
      exact le_of_not_gt (Nat.find_min (scale_next_fail_exists hp) hslt)

/-- The exact pair of cutoff inequalities used by the rounding argument. -/
theorem exists_scale {p : ℝ} (hp : 0 < p) :
    ∃ s : ℕ, p * scaleSum s ≤ 1 / 2 ∧ 1 / 2 < p * scaleSum (s + 1) :=
  ⟨maxScale p, maxScale_admissible hp, maxScale_next_fail hp⟩

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ColorMean ----
namespace OAI

/-!
# The mean of the numerical color variable

The variable at color `c` is `512^4 / 512^(c.val+1)`. This quotient represents
a possibly negative integral exponent without natural
subtraction. The computation includes the residual last color and also
applies when the selected number of scales is zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

theorem rounding_constant_pos : 0 < (25 : ℝ) * (512 : ℝ) ^ 4 := by positivity

/-- The leading constant is 25. -/
theorem five_Bfour_mul_scaled_density (r : ℝ) :
    5 * (512 : ℝ) ^ 4 * (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) = r / 5 := by
  field_simp
  ring

/-- The mean bound at the exact density used for rounding. -/
theorem color_mean_le_r_div_five {r : ℝ} (hr : 0 < r) {s : ℕ}
    (hs : (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) * scaleSum s ≤ 1 / 2)
    (hnext : 1 / 2 < (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) * scaleSum (s + 1)) :
    (∑ c : Color s,
      colorProb (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) s c *
        ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤ r / 5 := by
  simpa only [five_Bfour_mul_scaled_density] using
    color_mean_le (div_pos hr rounding_constant_pos) hs hnext

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorGlobalCost ----
namespace OAI

/-!
# The global cost of actual selected moves

Partition selected pairs first by their final coloring and then by their
full profile. The profile estimate removes the profile-dependent heavy
sets before summation. Word-count normalization and the finite geometric
bound then give the strict budget under the actual coloring law.
-/

noncomputable section

open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

/-- The same bound in expectation notation, ready for the bad-event argument. -/
theorem weighted_bad_selected_cost_le (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2) :
    (∑ a : Coloring α s, if Bad mu a then
      colorMass p s a * ∑ z ∈ selectedMoves mu a, p ^ (changes a z).card else 0) ≤ 1 / 20 := by
  classical
  simpa only [Finset.sum_filter, Finset.mul_sum] using
    (selected_total_cost_lt_one_twentieth mu p s hp hs).le

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorAverageColor ----
namespace OAI

/-!
# Average color from simultaneous capture

An integer color is one plus the number of preceding prefixes it misses.
Summing this finite identity against the actual probability mass gives the
mean-color identity. A captured coloring has the same family member at
every scale, so the geometric sum of its missed masses is at most one.
-/

namespace TalagrandThreshold.Selector

open scoped BigOperators

/-- The finite integer layer-cake identity for the zero-based color index. -/
theorem color_level_eq_one_add_tail {s : ℕ} (c : Color s) :
    (c.val + 1 : ℝ) = 1 + ∑ i : Fin s, if i.val < c.val then (1 : ℝ) else 0 := by
  rw [sum_color_tail_indicators]
  ring

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- The mass of colors above a prefixSet is its complementary mass. -/
theorem sum_tail_eq_one_sub_prefix {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s) (i : Fin s) :
    (∑ x, if i.val < (a x).val then mu.weight H x else 0) =
      1 - ∑ x ∈ prefixSet a i, mu.weight H x := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x : α => (a x).val ≤ i.val) (mu.weight H)
  rw [mu.total H] at hsplit
  have heq : (∑ x ∈ prefixSet a i, mu.weight H x) +
      (∑ x, if i.val < (a x).val then mu.weight H x else 0) = 1 := by
    simpa only [prefixSet, Finset.sum_filter, not_le] using hsplit
  exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using heq)

omit [DecidableEq α] in
/-- The actual mean color is one plus the sum of all missed prefixSet masses. -/
theorem meanColor_eq_one_add_sum_tail {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s) :
    meanColor mu H a = 1 +
      ∑ i : Fin s, (1 - ∑ x ∈ prefixSet a i, mu.weight H x) := by
  classical
  unfold meanColor
  simp_rw [color_level_eq_one_add_tail, add_mul, one_mul, Finset.sum_mul,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib, mu.total H, Finset.sum_comm]
  simp_rw [sum_tail_eq_one_sub_prefix mu H a]

/-- The truncation scales have total mass at most one, also when there are no scales. -/
theorem sum_dscale_le_one (s : ℕ) : (∑ i : Fin s, dscale i) ≤ 1 := by
  simpa only [dscale, one_div, inv_pow] using half_geometric_sum_le_one s

omit [DecidableEq α] in
/-- A single member capturing every prefixSet has mean color at most two. -/
theorem meanColor_le_two_of_capture {F : Family α} (mu : MassFamily F) {s : ℕ}
    (H : ↥F) (a : Coloring α s)
    (hcapture : ∀ i : Fin s,
      1 - dscale i ≤ ∑ x ∈ prefixSet a i, mu.weight H x) :
    meanColor mu H a ≤ 2 := by
  rw [meanColor_eq_one_add_sum_tail]
  calc
    1 + ∑ i : Fin s, (1 - ∑ x ∈ prefixSet a i, mu.weight H x) ≤
        1 + ∑ i : Fin s, dscale i := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i _
      linarith [hcapture i]
    _ ≤ 1 + 1 := add_le_add le_rfl (sum_dscale_le_one s)
    _ = 2 := by norm_num

omit [DecidableEq α] in
/-- The same captured member supplies the average-color witness. -/
theorem Captured.exists_meanColor_le_two {F : Family α} {mu : MassFamily F} {s : ℕ}
    {a : Coloring α s} (h : Captured mu a) : ∃ H : ↥F, meanColor mu H a ≤ 2 := by
  obtain ⟨H, hH⟩ := h
  exact ⟨H, meanColor_le_two_of_capture mu H a hH⟩

end TalagrandThreshold.Selector

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.SelectorMain ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The simultaneous multiscale selector

The actual minimum-move cover bounds the bad probability from below by its
weighted cost. The profile reconstruction and counting theorem bounds that
same cost from above. Both conclusions use the literal independent color law.
-/

noncomputable section
open scoped BigOperators Classical

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The actual bad event has probability at most one tenth. -/
theorem bad_probability_le_one_tenth {F : Family α}
    (mu : MassFamily F) (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (hF : ¬ Small p F) :
    (coloringLaw (α := α) p s hp hs).prob (Bad mu) ≤ 1 / 10 := by
  have hcover := half_bad_probability_le_selected_cost mu p s hp hs hF
  have hcount := weighted_bad_selected_cost_le mu p s hp hs
  linarith

/-- One family member is simultaneously captured at every scale. -/
theorem simultaneous_capture (F : Family α) (_hF : F.Nonempty)
    (_hsets : ∀ H ∈ F, H.Nonempty) (mu : MassFamily F)
    (p : ℝ) (hp0 : 0 < p) (_hp1 : p ≤ 1) (hnotsmall : ¬ Small p F)
    (s : ℕ) (hs : p * scaleSum s ≤ 1 / 2) :
    (9 / 10 : ℝ) ≤
      (coloringLaw (α := α) p s hp0 hs).prob (Captured mu) := by
  have hbad := bad_probability_le_one_tenth mu p s hp0 hs hnotsmall
  have hcompl := (coloringLaw (α := α) p s hp0 hs).prob_compl (Captured mu)
  change (coloringLaw (α := α) p s hp0 hs).prob (fun a => ¬ Captured mu a) ≤
    1 / 10 at hbad
  linarith

/-- With probability at least nine tenths, one member has mean color at most two. -/
theorem average_color (F : Family α) (hF : F.Nonempty)
    (hsets : ∀ H ∈ F, H.Nonempty) (mu : MassFamily F)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hnotsmall : ¬ Small p F)
    (s : ℕ) (hs : p * scaleSum s ≤ 1 / 2) :
    (9 / 10 : ℝ) ≤ (coloringLaw (α := α) p s hp0 hs).prob
      (fun a => ∃ H : ↥F, meanColor mu H a ≤ 2) := by
  exact (simultaneous_capture F hF hsets mu p hp0 hp1 hnotsmall s hs).trans
    ((coloringLaw (α := α) p s hp0 hs).prob_mono
      fun _ ha => ha.exists_meanColor_le_two)

end TalagrandThreshold.Selector

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.RoundingMain ----
namespace OAI

/-!
# Actual rounding of an unrestricted fractional cover

The concrete member masses feed the proved multiscale selector. The same
independent color law supplies the lower and upper bounds on the subset-product
score. No selector hypothesis or bound on support sizes appears in the result.
-/

open scoped BigOperators

noncomputable section

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem fractionalCover_empty_not_mem {F : Family α} {g : Finset α → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hcover : FractionalCover F g) (hcost : fracCost r g ≤ 1 / 2) :
    (∅ : Finset α) ∉ F := by
  intro hempty
  have hcoverEmpty : (1 : ℝ) ≤ g ∅ := by
    simpa only [Finset.powerset_empty, Finset.sum_singleton] using hcover.2 ∅ hempty
  have hweight : g ∅ ≤ (1 / 2 : ℝ) :=
    (empty_weight_le_fracCost hr hcover.nonneg).trans hcost
  exact (by norm_num : ¬ ((1 : ℝ) ≤ 1 / 2)) (hcoverEmpty.trans hweight)

/-- Every fractional cover of cost at most one half rounds at the exact
parameter `r / (25 * 512^4)`. Its support may contain subsets of any size. -/
theorem fractionalCover_rounding (F : Family α) (g : Finset α → ℝ) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hcover : FractionalCover F g)
    (hcost : fracCost r g ≤ 1 / 2) :
    Small (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) F := by
  classical
  by_cases hF : F.Nonempty
  · let p : ℝ := r / ((25 : ℝ) * (512 : ℝ) ^ 4)
    have hp0 : 0 < p := div_pos hr0 rounding_constant_pos
    have hp1 : p ≤ 1 := (div_le_one rounding_constant_pos).mpr
      (hr1.trans (by norm_num : (1 : ℝ) ≤ (25 : ℝ) * (512 : ℝ) ^ 4))
    have hnoempty := fractionalCover_empty_not_mem hr0.le hcover hcost
    let mu := fractionalMassFamily F g hr0.le hcover hcost
    obtain ⟨s, hs, hnext⟩ := exists_scale hp0
    let μ := coloringLaw (α := α) p s hp0 hs
    let Y : Color s → ℝ := fun c => (512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1)
    let Z : Coloring α s → ℝ := fun a => productScore g (fun x => Y (a x))
    let P : Coloring α s → Prop := fun a => ∃ H : ↥F, Selector.meanColor mu H a ≤ 2
    change Small p F
    by_contra hnotsmall
    have hprob : (9 / 10 : ℝ) ≤ μ.prob P :=
      Selector.average_color F hF (fun H hH => members_nonempty hnoempty hH)
        mu p hp0 hp1 hnotsmall s hs
    have hY : ∀ c, 0 ≤ Y c := by
      intro c
      exact div_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
    have hZ : ∀ a, 0 ≤ Z a := fun a =>
      productScore_nonneg hcover.nonneg (fun x => hY (a x))
    have hlower : ∀ a, P a → (1 / 4 : ℝ) ≤ Z a := by
      intro a ha
      obtain ⟨H, hH⟩ := ha
      apply productScore_lower_of_mean g H.val (fun x => (a x).val + 1) hcover.nonneg
        (memberMass_ge_half hcover H.property hr0.le hcost)
      simpa only [Selector.meanColor, mu, fractionalMassFamily, Nat.cast_add,
        Nat.cast_one] using hH
    have hmean : (colorLaw p s hp0 hs).expectation Y ≤ r / 5 := by
      change (∑ c : Color s,
        colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤ r / 5
      exact color_mean_le_r_div_five hr0 hs hnext
    have hupper : μ.expectation Z ≤ (1 / 10 : ℝ) :=
      expectation_productScore_le_tenth (colorLaw p s hp0 hs) g Y
        hcover.nonneg hY hr0.le hmean hcost
    exact rounding_expectation_contradiction μ P Z hZ hprob hlower hupper
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    rw [hFempty]
    exact small_empty _

end TalagrandThreshold

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.fractionalCover_rounding := @_root_.OAI.TalagrandThreshold.fractionalCover_rounding
