-- Prove2me | solution 1 for OAI.TalagrandThreshold.color_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T13:30:11.158764+00:00
-- url     : https://prove2.me/submissions/8673c3ca-b880-44fe-a1b8-e316c2cc9674

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/ColorMean.lean:L46-L67
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandThreshold.color_mean_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandThreshold_tail_lt_four_mul_p

-- ---- from OAI.Combinatorics.ExpectationThreshold.ProbabilityColors ----
namespace OAI

/-!
# The actual independent color law

Colors are indexed from zero; their numerical levels are one larger. The
first `s` colors have masses `256^(i+1) * p`, and the final color carries the
remaining mass. All laws below use these literal weights.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandThreshold

theorem scaleSum_nonneg (s : ℕ) : 0 ≤ scaleSum s := by
  exact Finset.sum_nonneg fun i _ => pow_nonneg (by norm_num) _

variable {α : Type*} [Fintype α]

variable [DecidableEq α]

end TalagrandThreshold

end

end OAI

-- ---- from OAI.Combinatorics.ExpectationThreshold.ScaleBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

private theorem color_mean_row (p : ℝ) (n : ℕ) :
    ((256 : ℝ) ^ n * p) * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ n) =
      (512 : ℝ) ^ 4 * (p * (1 / 2 : ℝ) ^ n) := by
  have hratio : (256 : ℝ) ^ n / (512 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
    rw [← div_pow]
    norm_num
  calc
    _ = (512 : ℝ) ^ 4 * (p * ((256 : ℝ) ^ n / (512 : ℝ) ^ n)) := by ring
    _ = _ := by rw [hratio]

/-- The exact finite-color mean, including the residual last color. -/
theorem color_mean_eq (p : ℝ) (s : ℕ) :
    (∑ c : Color s,
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) =
      (512 : ℝ) ^ 4 *
        (p * (∑ i : Fin s, (1 / 2 : ℝ) ^ (i.val + 1)) +
          (1 - p * scaleSum s) * (1 / (512 : ℝ) ^ (s + 1))) := by
  change (∑ c : Fin (s + 1),
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) = _
  rw [Fin.sum_univ_castSucc]
  simp only [colorProb_castSucc, colorProb_last, Fin.val_castSucc, Fin.val_last]
  simp_rw [color_mean_row]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Maximality of the scale makes the common mean at most `5 * 512^4 * p`. -/
theorem color_mean_le {p : ℝ} (hp : 0 < p) {s : ℕ}
    (_hs : p * scaleSum s ≤ 1 / 2)
    (hnext : 1 / 2 < p * scaleSum (s + 1)) :
    (∑ c : Color s,
      colorProb p s c * ((512 : ℝ) ^ 4 / (512 : ℝ) ^ (c.val + 1))) ≤
      5 * (512 : ℝ) ^ 4 * p := by
  have hres : 1 - p * scaleSum s ≤ 1 :=
    sub_le_self _ (mul_nonneg hp.le (scaleSum_nonneg s))
  have htail : (1 - p * scaleSum s) * (1 / (512 : ℝ) ^ (s + 1)) ≤ 4 * p := by
    calc
      _ ≤ 1 * (1 / (512 : ℝ) ^ (s + 1)) :=
        mul_le_mul_of_nonneg_right hres (by positivity)
      _ ≤ 4 * p := by
        simpa only [one_mul] using (tail_lt_four_mul_p hp hnext).le
  rw [color_mean_eq]
  calc
    _ ≤ (512 : ℝ) ^ 4 * (p * 1 + 4 * p) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left (half_geometric_sum_le_one s) hp.le) htail)
        (by positivity)
    _ = 5 * (512 : ℝ) ^ 4 * p := by ring

end TalagrandThreshold

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandThreshold
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandThreshold.color_mean_le := @_root_.OAI.TalagrandThreshold.color_mean_le
