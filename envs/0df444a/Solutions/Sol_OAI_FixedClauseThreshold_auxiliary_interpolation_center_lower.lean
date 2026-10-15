-- Prove2me | solution 1 for OAI.FixedClauseThreshold.auxiliary_interpolation_center_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:49:35.282056+00:00
-- url     : https://prove2.me/submissions/2569d639-0abe-4067-b52b-68ee69d934ed

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterComparison.lean:L18-L91
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.auxiliary_interpolation_center_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Theorems.Thm_OAI_FixedClauseThreshold_auxiliaryProbability_center_lower
import Theorems.Thm_OAI_FixedClauseThreshold_auxiliary_interpolation
import Theorems.Thm_OAI_FixedClauseThreshold_product_lower_two_deviations

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.ClauseProcess ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem alive_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ alive S := by
  unfold alive
  split <;> norm_num

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Binomial ----
namespace OAI

/-!
Finite Bernoulli-count expectations and integrated telescoping estimates.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem binomialMean_congr {p : ℝ} {m : ℕ} {f g : ℕ → ℝ}
    (h : ∀ d ≤ m, f d = g d) : binomialMean p m f = binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    simp only [binomialMean]
    rw [ih (fun d hd => h d (by omega)), ih (fun d hd => h (d + 1) (by omega))]

theorem binomialMean_const (p c : ℝ) (m : ℕ) : binomialMean p m (fun _ => c) = c := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_add (p : ℝ) (m : ℕ) (f g : ℕ → ℝ) :
    binomialMean p m (fun d => f d + g d) = binomialMean p m f + binomialMean p m g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_sub (p : ℝ) (m : ℕ) (f g : ℕ → ℝ) :
    binomialMean p m (fun d => f d - g d) = binomialMean p m f - binomialMean p m g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_mul_const (p c : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binomialMean p m (fun d => f d * c) = binomialMean p m f * c := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_const_mul (p c : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binomialMean p m (fun d => c * f d) = c * binomialMean p m f := by
  simpa only [mul_comm] using binomialMean_mul_const p c m f

theorem binomialMean_mono {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : ℕ → ℝ} (h : ∀ d ≤ m, f d ≤ g d) : binomialMean p m f ≤ binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h d (by omega))) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h (d + 1) (by omega))) hp0)

theorem binomialMean_id (p : ℝ) (m : ℕ) :
    binomialMean p m (fun d => (d : ℝ)) = (m : ℝ) * p := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    simp only [binomialMean, Nat.cast_add, Nat.cast_one, binomialMean_add,
      binomialMean_const, ih]
    ring

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Concentration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem fluctuationWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < fluctuationWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem auxiliarySurvival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    auxiliarySurvival k (m + 1) S = uniformMean (fun C : AuxiliaryClause n k =>
      auxiliarySurvival k m (S.filter (fun σ => auxiliarySatisfies σ C))) := by
  unfold auxiliarySurvival
  rw [Function.iterate_succ_apply']
  rfl

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Transfer ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
The exact probability of distinct variables, birthday bounds, and deletion and
thinning comparisons transfer auxiliary probabilities to the proper-clause law.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem auxiliarySurvival_nonneg {n k : ℕ} (m : ℕ) (S : Finset (Assignment n)) :
    0 ≤ auxiliarySurvival k m S := by
  induction m generalizing S with
  | zero => exact alive_nonneg S
  | succ m ih => rw [auxiliarySurvival_succ]; exact uniformMean_nonneg (fun _ => ih _)

theorem auxiliaryProbability_nonneg (n k m : ℕ) : 0 ≤ auxiliaryProbability n k m :=
  auxiliarySurvival_nonneg _ _

theorem transferFactor_pos (k : ℕ) : 0 < transferFactor k := Real.exp_pos _

theorem transferLower_pos (k : ℕ) : 0 < transferLower k := div_pos (transferFactor_pos k) (by norm_num)

theorem binomialMean_square (p : ℝ) (m : ℕ) :
    binomialMean p m (fun j => (j : ℝ)^2) = m * p * (1 - p) + ((m : ℝ) * p)^2 := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [binomialMean]
    have he : binomialMean p m (fun j => ((j + 1 : ℕ) : ℝ)^2) =
        binomialMean p m (fun j => (j : ℝ)^2) + 2 * ((m : ℝ) * p) + 1 := by
      calc
        _ = binomialMean p m (fun j => (j : ℝ)^2 + 2 * j + 1) := by
          apply binomialMean_congr
          intro j _
          push_cast
          ring
        _ = _ := by
          rw [binomialMean_add, binomialMean_add, binomialMean_const_mul,
            binomialMean_id, binomialMean_const]
    rw [he, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem binomialMean_centered_square (p : ℝ) (m : ℕ) :
    binomialMean p m (fun j => ((j : ℝ) - (m : ℝ) * p)^2) = (m : ℝ) * p * (1 - p) := by
  calc
    _ = binomialMean p m (fun j => (j : ℝ)^2 - 2 * ((m : ℝ) * p) * j + ((m : ℝ) * p)^2) := by
      apply binomialMean_congr
      intro j _
      ring
    _ = _ := by
      rw [binomialMean_add, binomialMean_sub, binomialMean_const_mul,
        binomialMean_const, binomialMean_square, binomialMean_id]
      ring

theorem binomialMean_div_const (p c : ℝ) (m : ℕ) (f : ℕ → ℝ) :
    binomialMean p m (fun j => f j / c) = binomialMean p m f / c := by
  simp only [div_eq_mul_inv, binomialMean_mul_const]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.CenterComparison ----
namespace OAI

/-!
Partition interpolation and concentration yield summable-error comparisons
for centers of two blocks and of neighboring sizes.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem auxiliary_interpolation_center_lower {r s k m : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hm : (m : ℝ) ≤ (capMultiplier k : ℝ) * ((r : ℝ) + s))
    (hgapr : (m : ℝ) * ((r : ℝ) / (r + s)) + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k)
    (hgaps : (m : ℝ) * ((s : ℝ) / (r + s)) + 2 * fluctuationWindow s k ≤ (s : ℝ) * center s k) :
    (transferLower k)^2 * (1 - samplingError r k - samplingError s k) ≤
      auxiliaryProbability (r + s) k m := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  let p : ℝ := (r : ℝ) / (r + s)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    apply (div_le_one (by positivity : (0 : ℝ) < r + s)).mpr
    linarith
  have hpq : 1 - p = (s : ℝ) / (r + s) := by dsimp [p]; field_simp; ring
  have hwr := fluctuationWindow_pos (k := k) hr0
  have hws := fluctuationWindow_pos (k := k) hs0
  have hpoint : ∀ j ≤ m,
      (transferLower k)^2 * (1 - ((j : ℝ) - m * p)^2 / (fluctuationWindow r k)^2 -
        ((j : ℝ) - m * p)^2 / (fluctuationWindow s k)^2) ≤
      auxiliaryProbability r k j * auxiliaryProbability s k (m - j) := by
    intro j hj
    apply product_lower_two_deviations (transferLower_pos k).le (by positivity) (by positivity)
      (auxiliaryProbability_nonneg r k j) (auxiliaryProbability_nonneg s k (m - j))
    · intro hdev
      apply auxiliaryProbability_center_lower hk hr hrrep hrerr
      have hsq : ((j : ℝ) - m * p)^2 < (fluctuationWindow r k)^2 :=
        (div_lt_one (sq_pos_of_pos hwr)).mp hdev
      by_contra hgap
      have hdiff : fluctuationWindow r k < (j : ℝ) - m * p := by
        change (m : ℝ) * p + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k at hgapr
        linarith
      nlinarith
    · intro hdev
      apply auxiliaryProbability_center_lower hk hs hsrep hserr
      have hsq : ((j : ℝ) - m * p)^2 < (fluctuationWindow s k)^2 :=
        (div_lt_one (sq_pos_of_pos hws)).mp hdev
      rw [← hpq] at hgaps
      rw [Nat.cast_sub hj]
      by_contra hgap
      have hdiff : fluctuationWindow s k < -((j : ℝ) - m * p) := by linarith
      nlinarith
  have hmean := binomialMean_mono hp0 hp1 hpoint
  rw [binomialMean_const_mul, binomialMean_sub, binomialMean_sub, binomialMean_const,
    binomialMean_div_const, binomialMean_div_const, binomialMean_centered_square] at hmean
  apply le_trans _ (hmean.trans (auxiliary_interpolation hr0 hs0 m))
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hmp : (m : ℝ) * p ≤ (capMultiplier k : ℝ) * r := by
    have h := mul_le_mul_of_nonneg_right hm hp0
    have he : ((capMultiplier k : ℝ) * ((r : ℝ) + s)) * p =
        (capMultiplier k : ℝ) * r := by dsimp [p]; field_simp
    simpa only [he] using h
  have hmq : (m : ℝ) * (1 - p) ≤ (capMultiplier k : ℝ) * s := by
    have h := mul_le_mul_of_nonneg_right hm (sub_nonneg.mpr hp1)
    have he : ((capMultiplier k : ℝ) * ((r : ℝ) + s)) * (1 - p) =
        (capMultiplier k : ℝ) * s := by rw [hpq]; field_simp
    simpa only [he] using h
  have hvr : (m : ℝ) * p * (1 - p) ≤ (capMultiplier k : ℝ) * r := by
    have h := mul_le_mul_of_nonneg_left (show 1 - p ≤ 1 by linarith)
      (mul_nonneg (Nat.cast_nonneg m) hp0)
    nlinarith
  have hvs : (m : ℝ) * p * (1 - p) ≤ (capMultiplier k : ℝ) * s := by
    have h := mul_le_mul_of_nonneg_left hp1
      (mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr hp1))
    nlinarith
  have hfr := div_le_div_of_nonneg_right hvr (sq_nonneg (fluctuationWindow r k))
  have hfs := div_le_div_of_nonneg_right hvs (sq_nonneg (fluctuationWindow s k))
  unfold samplingError
  linarith

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.auxiliary_interpolation_center_lower := @_root_.OAI.FixedClauseThreshold.auxiliary_interpolation_center_lower
