-- Prove2me | solution 1 for OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T14:21:15.167983+00:00
-- url     : https://prove2.me/submissions/1a3ffaa7-21be-4e87-9e66-bf6e666bd5a2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/Main.lean:L18-L39
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TalagrandThreshold_talagrand_expectation_threshold_equivalence) verbatim and is proved by it.
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
import Theorems.Thm_OAI_TalagrandThreshold_fractionalCover_rounding
import Theorems.Thm_OAI_TalagrandThreshold_isCompact_fractionalFeasible

-- ---- from OAI.Combinatorics.ExpectationThreshold.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
theorem covers_self (F : Family α) : Covers F F :=
  fun H hH => ⟨H, hH, Finset.Subset.refl H⟩

omit [Fintype α] [DecidableEq α] in
theorem members_nonempty {F : Family α} (hF : (∅ : Finset α) ∉ F)
    {H : Finset α} (hH : H ∈ F) : H.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  exact hF (he ▸ hH)

omit [Fintype α] [DecidableEq α] in
theorem cost_zero_of_empty_not_mem (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    cost 0 F = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  exact zero_pow (Nat.ne_of_gt (Finset.card_pos.mpr (members_nonempty hF hS)))

omit [Fintype α] [DecidableEq α] in
theorem small_zero (F : Family α) (hF : (∅ : Finset α) ∉ F) : Small 0 F := by
  refine ⟨F, covers_self F, ?_⟩
  rw [cost_zero_of_empty_not_mem F hF]
  exact div_nonneg zero_le_one zero_le_two

omit [DecidableEq α] in
theorem Increasing.empty_not_mem {F : Family α} (hF : Increasing F)
    (hproper : F ≠ Finset.univ) : (∅ : Finset α) ∉ F := by
  intro hempty
  apply hproper
  apply Finset.eq_univ_iff_forall.mpr
  intro H
  exact hF ∅ hempty H (Finset.empty_subset H)

omit [Fintype α] in
theorem coverIndicator_nonneg (G : Family α) (S : Finset α) :
    0 ≤ coverIndicator G S := by
  unfold coverIndicator
  split_ifs <;> simp

omit [Fintype α] in
theorem coverIndicator_le_one (G : Family α) (S : Finset α) :
    coverIndicator G S ≤ 1 := by
  unfold coverIndicator
  split_ifs <;> simp

omit [Fintype α] in
theorem Covers.fractionalCover {G F : Family α} (h : Covers G F) :
    FractionalCover F (coverIndicator G) := by
  constructor
  · intro S
    exact ⟨coverIndicator_nonneg G S, coverIndicator_le_one G S⟩
  · intro H hH
    obtain ⟨S, hSG, hSH⟩ := h H hH
    have hs := Finset.single_le_sum (fun T _ => coverIndicator_nonneg G T)
      (Finset.mem_powerset.mpr hSH)
    simpa only [coverIndicator, ite_eq_left hSG] using hs

theorem fracCost_coverIndicator (p : ℝ) (G : Family α) :
    fracCost p (coverIndicator G) = cost p G := by
  classical
  unfold fracCost cost
  calc
    (∑ S : Finset α, coverIndicator G S * p ^ S.card) =
        ∑ S : Finset α, if S ∈ G then p ^ S.card else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases hS : S ∈ G <;> simp [coverIndicator, hS]
    _ = ∑ S ∈ G, p ^ S.card := Finset.sum_ite_mem_eq G (fun S => p ^ S.card)

theorem Small.fractionalSmall {F : Family α} {p : ℝ} (h : Small p F) :
    FractionalSmall p F := by
  obtain ⟨G, hG, hcost⟩ := h
  exact ⟨coverIndicator G, hG.fractionalCover, (fracCost_coverIndicator p G).trans_le hcost⟩

theorem fractionalSmall_zero (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    FractionalSmall 0 F := (small_zero F hF).fractionalSmall

end
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

end TalagrandThreshold

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

/-- Parameterwise rounding also includes density zero, with an actual cover. -/
theorem fractionalSmall_rounding (F : Family α) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hF : FractionalSmall r F) :
    Small (r / ((25 : ℝ) * (512 : ℝ) ^ 4)) F := by
  obtain ⟨g, hcover, hcost⟩ := hF
  by_cases hr : r = 0
  · subst r
    rw [zero_div]
    exact small_zero F (fractionalCover_empty_not_mem le_rfl hcover hcost)
  · exact fractionalCover_rounding F g (lt_of_le_of_ne hr0 (Ne.symm hr)) hr1 hcover hcost

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ThresholdBounds ----
namespace OAI

/-!
# Elementary bounds for the actual expectation thresholds

When the empty set is absent from the family, zero is feasible for both
thresholds. Their feasible sets are bounded by one, and indicator covers
give the integral-to-fractional comparison.
-/

namespace TalagrandThreshold

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem integralFeasible_bddAbove (F : Family α) : BddAbove (integralFeasible F) :=
  ⟨1, fun _ hp => hp.2.1⟩

omit [DecidableEq α] in
theorem fractionalFeasible_bddAbove (F : Family α) : BddAbove (fractionalFeasible F) :=
  ⟨1, fun _ hp => hp.2.1⟩

theorem zero_mem_fractionalFeasible (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    (0 : ℝ) ∈ fractionalFeasible F :=
  ⟨le_rfl, zero_le_one, fractionalSmall_zero F hF⟩

theorem fractionalFeasible_nonempty (F : Family α) (hF : (∅ : Finset α) ∉ F) :
    (fractionalFeasible F).Nonempty :=
  ⟨0, zero_mem_fractionalFeasible F hF⟩

omit [Fintype α] [DecidableEq α] in
theorem le_q_of_mem {F : Family α} {p : ℝ} (hp : p ∈ integralFeasible F) :
    p ≤ q F :=
  le_csSup (integralFeasible_bddAbove F) hp

omit [DecidableEq α] in
theorem le_qf_of_mem {F : Family α} {p : ℝ} (hp : p ∈ fractionalFeasible F) :
    p ≤ qf F :=
  le_csSup (fractionalFeasible_bddAbove F) hp

omit [Fintype α] [DecidableEq α] in
theorem le_q_of_small {F : Family α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hp : Small p F) : p ≤ q F :=
  le_q_of_mem ⟨hp0, hp1, hp⟩

theorem qf_nonneg (F : Family α) (hF : (∅ : Finset α) ∉ F) : 0 ≤ qf F :=
  le_qf_of_mem (zero_mem_fractionalFeasible F hF)

theorem qf_le_one (F : Family α) (hF : (∅ : Finset α) ∉ F) : qf F ≤ 1 :=
  csSup_le (fractionalFeasible_nonempty F hF) (fun _ hp => hp.2.1)

end
end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ThresholdAttainment ----
namespace OAI

/-!
# Attainment of the integral and fractional thresholds

There are finitely many integral covers, so integral feasibility is closed
in the density interval. Fractional feasibility is a compact projection.
The actual suprema therefore belong to their respective feasible sets as
soon as those sets contain density zero.
-/

namespace TalagrandThreshold

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The fractional supremum is an actual feasible density. -/
theorem qf_mem_fractionalFeasible (F : Family α) (hF : ∅ ∉ F) :
    qf F ∈ fractionalFeasible F := by
  exact (isCompact_fractionalFeasible F).sSup_mem (fractionalFeasible_nonempty F hF)

theorem fractionalSmall_qf (F : Family α) (hF : ∅ ∉ F) : FractionalSmall (qf F) F :=
  (mem_fractionalFeasible.mp (qf_mem_fractionalFeasible F hF)).2.2

end TalagrandThreshold

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.Main ----
namespace OAI

/-!
# Integral and fractional expectation thresholds

The fractional threshold is genuinely attained with budget one half. Rounding
that attained cover gives an integral cover at the threshold divided by
`25 * 512^4`, still with budget one half and without a support-size restriction.
-/

namespace TalagrandThreshold

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Talagrand's threshold comparison with the explicit constant `25 * 512^4`.
The coefficient 25 is an integer factor, and both feasible sets use budget
one half. The fractional cover ranges over every subset of the ground set. -/
theorem talagrand_expectation_threshold_equivalence [Nonempty α]
    (F : Family α) (_hF : F.Nonempty) (hproper : F ≠ Finset.univ)
    (hIncreasing : Increasing F) :
    qf F ≤ ((25 : ℝ) * (512 : ℝ) ^ 4) * q F := by
  have hempty : (∅ : Finset α) ∉ F := hIncreasing.empty_not_mem hproper
  have hqf0 : 0 ≤ qf F := qf_nonneg F hempty
  have hqf1 : qf F ≤ 1 := qf_le_one F hempty
  have hsmall : Small (qf F / ((25 : ℝ) * (512 : ℝ) ^ 4)) F :=
    fractionalSmall_rounding F hqf0 hqf1 (fractionalSmall_qf F hempty)
  have hscaled0 : 0 ≤ qf F / ((25 : ℝ) * (512 : ℝ) ^ 4) :=
    div_nonneg hqf0 rounding_constant_pos.le
  have hscaled1 : qf F / ((25 : ℝ) * (512 : ℝ) ^ 4) ≤ 1 :=
    (div_le_one rounding_constant_pos).mpr
      (hqf1.trans (by norm_num : (1 : ℝ) ≤ (25 : ℝ) * (512 : ℝ) ^ 4))
  have hle := le_q_of_small hscaled0 hscaled1 hsmall
  calc
    qf F ≤ q F * ((25 : ℝ) * (512 : ℝ) ^ 4) :=
      (div_le_iff₀ rounding_constant_pos).mp hle
    _ = ((25 : ℝ) * (512 : ℝ) ^ 4) * q F := mul_comm _ _

end TalagrandThreshold

end OAI

-- ---- mission target ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

namespace OAI
namespace TalagrandThreshold
theorem _root_.solution [Nonempty α]
    (F : Family α) (_hF : F.Nonempty) (hproper : F ≠ Finset.univ)
    (hIncreasing : Increasing F) :
    qf F ≤ ((25 : ℝ) * (512 : ℝ) ^ 4) * q F := by
  first
    | exact OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence F _hF hproper hIncreasing
    | exact OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence
    | (apply OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence <;> assumption)
    | (intros; apply OAI.TalagrandThreshold.talagrand_expectation_threshold_equivalence <;> assumption)
end TalagrandThreshold
end OAI
