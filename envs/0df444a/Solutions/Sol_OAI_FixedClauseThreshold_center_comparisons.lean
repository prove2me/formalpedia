-- Prove2me | solution 1 for OAI.FixedClauseThreshold.center_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:56:18.279849+00:00
-- url     : https://prove2.me/submissions/7b32038e-f90d-4999-84e2-347db99d8c0d

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterComparison.lean:L344-L363
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.center_comparisons. The node keeps its source
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
import Theorems.Thm_OAI_FixedClauseThreshold_center_bounds_eventually
import Theorems.Thm_OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability
import Theorems.Thm_OAI_FixedClauseThreshold_center_sum_comparison_of_bounds

-- ---- from OAI.Probability.RandomSAT.Clauses ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Signed variable sets, clause cardinalities, and the exact probability of killing
a nonempty solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem nonempty_properClause {n k : ℕ} (hkn : k ≤ n) :
    Nonempty (ProperClause n k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_properClause]
  exact Nat.mul_pos (Nat.choose_pos hkn) (by positivity)

end

end FixedClauseThreshold

end OAI

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

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

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

theorem alive_le_one {n : ℕ} (S : Finset (Assignment n)) : alive S ≤ 1 := by
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

theorem binomialMean_const (p c : ℝ) (m : ℕ) : binomialMean p m (fun _ => c) = c := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [binomialMean, ih]; ring

theorem binomialMean_mono {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : ℕ → ℝ} (h : ∀ d ≤ m, f d ≤ g d) : binomialMean p m f ≤ binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    exact add_le_add
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h d (by omega))) (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left (ih (fun d hd => h (d + 1) (by omega))) hp0)

theorem binomialMean_nonneg {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (h : ∀ d ≤ m, 0 ≤ f d) : 0 ≤ binomialMean p m f := by
  simpa only [binomialMean_const] using binomialMean_mono hp0 hp1 h

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Variance ----
namespace OAI

/-!
Stopped satisfiable lifetimes, insertion delays, and the coordinate-omission
variance bound in terms of integrated forcing.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem lifetime_le {n k m : ℕ} (S : Finset (Assignment n)) (F : Formula n k m) :
    lifetime k m S F ≤ m := by
  induction m generalizing S with
  | zero => simp [lifetime]
  | succ m ih =>
    simp only [lifetime, Nat.cast_add, Nat.cast_one]
    linarith [alive_le_one (addClause S (F 0)), ih (addClause S (F 0)) (Fin.tail F)]

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

theorem delta_pos {k : ℕ} (hk : 3 ≤ k) : 0 < delta k := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  unfold delta
  exact div_pos (by linarith) (by positivity)

theorem delta_lt_half {k : ℕ} (hk : 3 ≤ k) : delta k < 1 / 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [delta, div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * k)]
  linarith

theorem eta_eq_twice_delta (k : ℕ) : eta k = 2 * delta k := by
  unfold eta delta
  ring

theorem center_le_capMultiplier {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    center n k ≤ capMultiplier k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := uniformMean_mono (fun F : Formula n k (mainCap n k) => lifetime_le Finset.univ F)
  rw [uniformMean_const] at h
  unfold center lifetimeMean
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  simpa [mainCap] using h

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.CenterBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem smallDensity_pos : 0 < smallDensity := by unfold smallDensity; positivity

theorem lowerCenterBound_pos : 0 < lowerCenterBound := div_pos smallDensity_pos (by norm_num)

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

theorem exp_neg_two_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ 1 - x by linarith)
  have hh : 1 ≤ Real.exp (2 * x) * (1 - x) := by nlinarith
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (2 * x))).mp
  rw [← Real.exp_add, show 2 * x + -2 * x = 0 by ring, Real.exp_zero]
  simpa only [mul_comm] using hh

theorem transferFactor_pos (k : ℕ) : 0 < transferFactor k := Real.exp_pos _

theorem transferLower_pos (k : ℕ) : 0 < transferLower k := div_pos (transferFactor_pos k) (by norm_num)

theorem binomialMean_all_success {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (m : ℕ) (f : ℕ → ℝ) (hf : ∀ j ≤ m, 0 ≤ f j) :
    p^m * f m ≤ binomialMean p m f := by
  induction m generalizing f with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [binomialMean, pow_succ]
    have h0 := binomialMean_nonneg hp0 hp1 (m := m) (f := f) (fun j hj => hf j (by omega))
    have h1 := ih (fun j => f (j + 1)) (fun j hj => hf (j + 1) (by omega))
    have hm := mul_le_mul_of_nonneg_left h1 hp0
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) h0]

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

theorem densityWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < densityWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem fluctuationWindow_eq_mul {n k : ℕ} (hn : 0 < n) :
    fluctuationWindow n k = (n : ℝ) * densityWindow n k := by
  unfold fluctuationWindow densityWindow
  rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hn), Real.rpow_one]

theorem densityWindow_antitone {r s k : ℕ} (hk : 3 ≤ k) (hr : 0 < r) (hrs : r ≤ s) :
    densityWindow s k ≤ densityWindow r k :=
  Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hr) (by exact_mod_cast hrs)
    (neg_nonpos.mpr (delta_pos hk).le)

theorem densityWindow_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => densityWindow n k) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (delta_pos hk)).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem concentrationError_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => concentrationError n k) Filter.atTop (nhds 0) := by
  have hη : 0 < eta k := by rw [eta_eq_twice_delta]; positivity [delta_pos hk]
  have ht := (tendsto_rpow_neg_atTop hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [concentrationError, Function.comp_apply, mul_zero] using ht.const_mul (varianceConstant k)

theorem samplingError_identity {n k : ℕ} (hn : 0 < n) :
    samplingError n k = (capMultiplier k : ℝ) * (n : ℝ)^(-(1 - 2 * delta k)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold samplingError fluctuationWindow
  rw [← Real.rpow_two ((n : ℝ)^(1 - delta k)), ← Real.rpow_mul hn'.le]
  have he : -(1 - 2 * delta k) = 1 - (1 - delta k) * 2 := by ring
  rw [he, Real.rpow_sub hn', Real.rpow_one]
  ring

theorem samplingError_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => samplingError n k) Filter.atTop (nhds 0) := by
  have hd : 0 < 1 - 2 * delta k := by linarith [delta_lt_half hk]
  have ht := (tendsto_rpow_neg_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht' : Filter.Tendsto (fun n : ℕ => (capMultiplier k : ℝ) * (n : ℝ)^(-(1 - 2 * delta k)))
      Filter.atTop (nhds 0) := by simpa only [Function.comp_apply, mul_zero] using ht.const_mul (capMultiplier k : ℝ)
  apply ht'.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (samplingError_identity (k := k) (by omega)).symm

theorem fluctuationWindow_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => fluctuationWindow n k) Filter.atTop Filter.atTop := by
  have hd : 0 < 1 - delta k := by linarith [delta_lt_half hk]
  exact (tendsto_rpow_atTop hd).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem neighborLower_pos (k : ℕ) : 0 < neighborLower k :=
  mul_pos (Real.exp_pos _) (transferLower_pos k)

theorem neighbor_all_left {s k m : ℕ} (hs : 0 < s) :
    ((s : ℝ) / (s + 1))^m * auxiliaryProbability s k m ≤ auxiliaryProbability (s + 1) k m := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hp0 : 0 ≤ (s : ℝ) / (s + 1) := by positivity
  have hp1 : (s : ℝ) / (s + 1) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < s + 1)).mpr
    linarith
  have h := binomialMean_all_success hp0 hp1 m
    (fun j => auxiliaryProbability s k j * auxiliaryProbability 1 k (m - j))
    (fun j _ => mul_nonneg (auxiliaryProbability_nonneg _ _ _) (auxiliaryProbability_nonneg _ _ _))
  simp only [Nat.sub_self, auxiliaryProbability_zero, mul_one] at h
  apply h.trans
  simpa only [Nat.cast_one] using (auxiliary_interpolation (k := k) hs (by omega : 0 < 1) m)

theorem neighbor_pow_lower {s k m : ℕ} (hs : 0 < s)
    (hm : (m : ℝ) ≤ (capMultiplier k : ℝ) * ((s : ℝ) + 1)) :
    neighborFactor k ≤ ((s : ℝ) / (s + 1))^m := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hN : (0 : ℝ) < s + 1 := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / ((s : ℝ) + 1) := by positivity
  have hx : (1 : ℝ) / ((s : ℝ) + 1) ≤ 1 / 2 := by
    apply (div_le_iff₀ hN).mpr
    linarith
  have hbase := exp_neg_two_le_one_sub hx0 hx
  have he : 1 - (1 : ℝ) / ((s : ℝ) + 1) = (s : ℝ) / (s + 1) := by field_simp; ring
  rw [he] at hbase
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hbase m
  rw [← Real.exp_nat_mul] at hpow
  apply le_trans _ hpow
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hm hx0
  have he' : (capMultiplier k : ℝ) * ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1)) = capMultiplier k := by field_simp
  rw [he'] at hh
  nlinarith

theorem center_neighbor_comparison_of_bounds {s k : ℕ} (hk : 3 ≤ k)
    (hs : k + 1 ≤ s) (hsrep : 2 * repeatPairs k ≤ s)
    (hserr : concentrationError s k ≤ 1 / 2)
    (hNerr : concentrationError (s + 1) k < neighborLower k)
    (hlow : 2 * densityWindow s k ≤ center s k)
    (hwindow : (capMultiplier k : ℝ) ≤ fluctuationWindow s k) :
    center s k - 4 * densityWindow s k ≤ center (s + 1) k := by
  have hs0 : 0 < s := by omega
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  let c := center s k - 2 * densityWindow s k
  have hc0 : 0 ≤ c := sub_nonneg.mpr hlow
  have hcenter := center_le_capMultiplier (by omega : k ≤ s) hs0
  have hcL : c ≤ capMultiplier k := by
    have hp := (densityWindow_pos (k := k) hs0).le
    dsimp [c]
    linarith
  let m := ⌊c * ((s : ℝ) + 1)⌋₊
  have hm : (m : ℝ) ≤ c * ((s : ℝ) + 1) := Nat.floor_le (by positivity)
  have hmL := hm.trans (mul_le_mul_of_nonneg_right hcL (by positivity : (0 : ℝ) ≤ (s : ℝ) + 1))
  have hgap : (m : ℝ) + fluctuationWindow s k ≤ (s : ℝ) * center s k := by
    have hw := fluctuationWindow_eq_mul (k := k) hs0
    have he : c * ((s : ℝ) + 1) = (s : ℝ) * center s k - 2 * fluctuationWindow s k + c := by
      rw [hw]
      dsimp [c]
      ring
    rw [he] at hm
    linarith
  have hlocal := auxiliaryProbability_center_lower hk hs hsrep hserr hgap
  have hpow := neighbor_pow_lower (k := k) hs0 hmL
  have hprod := mul_le_mul hpow hlocal (transferLower_pos k).le
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) / (s + 1)) m)
  have hprob : neighborLower k ≤ auxiliaryProbability (s + 1) k m :=
    hprod.trans (neighbor_all_left hs0)
  have hcN := center_lower_of_auxiliary_probability hk (by omega : k + 1 ≤ s + 1) hc0 hcL
    (show concentrationError (s + 1) k < auxiliaryProbability (s + 1) k ⌊c * ((s + 1 : ℕ) : ℝ)⌋₊ by
      simpa only [Nat.cast_add, Nat.cast_one] using hNerr.trans_le hprob)
  have hd := densityWindow_antitone hk hs0 (Nat.le_succ s)
  dsimp [c] at hcN
  linarith

theorem centerRegular_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop, CenterRegular k n := by
  have hsize : ∀ᶠ n : ℕ in Filter.atTop, k + 1 ≤ n := Filter.eventually_ge_atTop _
  have hrep := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Filter.eventually_ge_atTop (2 * repeatPairs k))
  have he := (concentrationError_tendsto k hk).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)
  have hs := (samplingError_tendsto k hk).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)
  have heSum := (concentrationError_tendsto k hk).eventually_lt_const
    (div_pos (sq_pos_of_pos (transferLower_pos k)) (by norm_num) : (0 : ℝ) < (transferLower k)^2 / 2)
  have heNeighbor := (concentrationError_tendsto k hk).eventually_lt_const (neighborLower_pos k)
  have hd := (densityWindow_tendsto k hk).eventually_lt_const
    (div_pos lowerCenterBound_pos (by norm_num) : (0 : ℝ) < lowerCenterBound / 2)
  have hw := (fluctuationWindow_tendsto k hk).eventually (Filter.eventually_ge_atTop (capMultiplier k : ℝ))
  filter_upwards [hsize, hrep, he, hs, heSum, heNeighbor, center_bounds_eventually k hk, hd, hw]
    with n hn hr he hs hes hen hc hd hw
  exact ⟨hn, hr, he.le, hs.le, hes, hen, hc.1, by linarith, hw⟩

theorem center_comparisons (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N,
        min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k) ∧
      (∀ s ≥ N, center s k - 4 * densityWindow s k ≤ center (s + 1) k) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (centerRegular_eventually k hk)
  refine ⟨N, ?_, ?_⟩
  · intro r hr s hs
    have hR := hN r hr
    have hS := hN s hs
    have hU := hN (min r s) (le_min hr hs)
    have hT := hN (r + s) (by omega)
    exact center_sum_comparison_of_bounds hk hR.size hS.size hR.repetition hS.repetition
      hR.error hS.error hR.sampling hS.sampling hT.sumError
      (hU.densitySmall.trans (le_min hR.centerLower hS.centerLower))
  · intro s hs
    have hS := hN s hs
    have hT := hN (s + 1) (by omega)
    exact center_neighbor_comparison_of_bounds hk hS.size hS.repetition hS.error hT.neighborError
      (hS.densitySmall.trans hS.centerLower) hS.windowLarge

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.center_comparisons := @_root_.OAI.FixedClauseThreshold.center_comparisons
