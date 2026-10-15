-- Prove2me | solution 1 for OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:52:16.814452+00:00
-- url     : https://prove2.me/submissions/61ffae56-7af4-4011-b13f-dd8fe28d08c3

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterComparison.lean:L148-L167
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability. The node keeps its source
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
import Theorems.Thm_OAI_FixedClauseThreshold_clauseAverage_alive
import Theorems.Thm_OAI_FixedClauseThreshold_concentration_capped
import Theorems.Thm_OAI_FixedClauseThreshold_embeddedAverage_alive
import Theorems.Thm_OAI_FixedClauseThreshold_finiteClauseAverage_commute
import Theorems.Thm_OAI_FixedClauseThreshold_killFraction_le_pow
import Theorems.Thm_OAI_FixedClauseThreshold_properSATProbability_eq_survival

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

theorem uniformProbability_mono {α : Type*} [Fintype α] {p q : α → Prop}
    (hpq : ∀ a, p a → q a) : uniformProbability p ≤ uniformProbability q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective
    (fun a : {a // p a} => (⟨a.val, hpq a.val a.property⟩ : {a // q a}))
    (fun _ _ h => Subtype.ext (congrArg (fun t : {a // q a} => t.val) h))

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Replacement ----
namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_congr {α : Type*} [Fintype α] {p q : α → Prop}
    (h : ∀ a, p a ↔ q a) : uniformProbability p = uniformProbability q := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquivRight h)]

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

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

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

theorem addClause_subset {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    addClause S C ⊆ S := Finset.filter_subset _ _

theorem lifetime_nonneg {n k m : ℕ} (S : Finset (Assignment n)) (F : Formula n k m) :
    0 ≤ lifetime k m S F := by
  induction m generalizing S with
  | zero => exact le_rfl
  | succ m ih => exact add_nonneg (alive_nonneg _) (ih _ _)

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

theorem uniformProbability_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (p : (Fin (m + 1) → α) → Prop) :
    uniformProbability p = uniformMean (fun C : α => uniformProbability
      (fun F : Fin m → α => p (Fin.cons C F))) := by
  rw [uniformProbability_eq_mean, uniformMean_fin_succ]
  apply uniformMean_congr
  intro C
  exact (uniformProbability_eq_mean _).symm

theorem lifetime_tail_probability {n k m M : ℕ} (hkn : k ≤ n) (hm : m ≤ M)
    (S : Finset (Assignment n)) :
    uniformProbability (fun F : Formula n k M => S.Nonempty ∧ (m : ℝ) ≤ lifetime k M S F) =
      survival k m S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  induction m generalizing M S with
  | zero =>
    rw [uniformProbability_eq_mean, survival_zero]
    have he : (fun F : Formula n k M => if S.Nonempty ∧ (0 : ℝ) ≤ lifetime k M S F
        then (1 : ℝ) else 0) = fun _ => alive S := by
      funext F
      simp only [and_iff_left (lifetime_nonneg S F), alive]
    simp only [Nat.cast_zero, he, uniformMean_const]
  | succ m ih =>
    cases M with
    | zero => omega
    | succ M =>
      rw [uniformProbability_fin_succ]
      have he (C : ProperClause n k) (F : Formula n k M) :
          (S.Nonempty ∧ ((m + 1 : ℕ) : ℝ) ≤ lifetime k (M + 1) S (Fin.cons C F)) ↔
          (addClause S C).Nonempty ∧ (m : ℝ) ≤ lifetime k M (addClause S C) F := by
        rw [lifetime_cons, Nat.cast_add, Nat.cast_one]
        by_cases hC : (addClause S C).Nonempty
        · have hS : S.Nonempty := hC.mono (addClause_subset S C)
          simp only [hS, hC, alive, ite_true, true_and]
          constructor <;> intro h <;> linarith
        · have hempty : addClause S C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
          simp only [hempty, alive_empty, lifetime_empty, add_zero, Finset.not_nonempty_empty,
            false_and]
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
          constructor
          · rintro ⟨_, hh⟩; linarith
          · exact False.elim
      rw [survival_succ]
      apply uniformMean_congr
      intro C
      exact (uniformProbability_congr (he C)).trans (ih (M := M) (by omega) (addClause S C))

theorem properSATProbability_eq_lifetime_tail {n k m M : ℕ} (hkn : k ≤ n) (hm : m ≤ M) :
    properSATProbability n k m = uniformProbability (fun F : Formula n k M =>
      (m : ℝ) ≤ lifetime k M Finset.univ F) := by
  rw [properSATProbability_eq_survival, ← lifetime_tail_probability hkn hm]
  congr 1
  funext F
  simp

theorem delta_lt_half {k : ℕ} (hk : 3 ≤ k) : delta k < 1 / 2 := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  rw [delta, div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * k)]
  linarith

theorem properSATProbability_center_upper {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
    properSATProbability n k m ≤ concentrationError n k := by
  rw [properSATProbability_eq_lifetime_tail (by omega) hm]
  apply (uniformProbability_mono (fun F hF => ?_)).trans (concentration_capped hk hn)
  exact le_trans (by linarith) (le_abs_self _)

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

theorem finiteClauseAverage_mono {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, finiteClauseAverage sat f S ≤ finiteClauseAverage sat g S := by
  intro S
  exact uniformMean_mono (fun c => hfg _)

theorem iterate_compare_of_commute {X : Type*}
    (A B : (X → ℝ) → (X → ℝ)) (hA : Monotone A) (hB : Monotone B)
    (hcomm : Function.Commute A B) {f : X → ℝ} (hf : B f ≤ A f) (m : ℕ) :
    B^[m] f ≤ A^[m] f := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      B (B^[m] f) ≤ B (A^[m] f) := hB ih
      _ = A^[m] (B f) := (hcomm.symm.iterate_right m f)
      _ ≤ A^[m] (A f) := hA.iterate m hf
      _ = A (A^[m] f) := (Function.iterate_succ_apply A m f).symm.trans
        (Function.iterate_succ_apply' A m f)

theorem auxiliaryAverage_alive {n k : ℕ} (hn : 0 < n) (S : Finset (Assignment n)) :
    auxiliaryAverage k alive S = alive S * (1 - (forcedFraction S / 2)^k) := by
  rw [auxiliaryAverage, embeddedAverage_alive hn, embeddedForced_id]
  congr 2
  unfold forcedFraction
  ring

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

theorem auxiliaryAverage_le_proper {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    auxiliaryAverage k alive ≤ clauseAverage (n := n) k alive := by
  intro S
  rw [auxiliaryAverage_alive hn, clauseAverage_alive hkn]
  apply mul_le_mul_of_nonneg_left _ (alive_nonneg S)
  apply sub_le_sub_left
  have hb : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := killFraction_le_pow hb hkn hn
  simpa only [forcedFraction, div_mul_eq_div_div_swap] using h

theorem auxiliaryProbability_le_proper {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (m : ℕ) :
    auxiliaryProbability n k m ≤ properSATProbability n k m := by
  rw [properSATProbability_eq_survival]
  exact iterate_compare_of_commute (clauseAverage k) (auxiliaryAverage k)
    (fun _ _ h => finiteClauseAverage_mono _ h) (fun _ _ h => finiteClauseAverage_mono _ h)
    (finiteClauseAverage_commute _ _) (auxiliaryAverage_le_proper hn hkn) m Finset.univ

theorem auxiliaryProbability_center_upper {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
    auxiliaryProbability n k m ≤ concentrationError n k :=
  (auxiliaryProbability_le_proper (by omega) (by omega) m).trans
    (properSATProbability_center_upper hk hn hm hgap)

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

theorem fluctuationWindow_eq_mul {n k : ℕ} (hn : 0 < n) :
    fluctuationWindow n k = (n : ℝ) * densityWindow n k := by
  unfold fluctuationWindow densityWindow
  rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hn), Real.rpow_one]

theorem fluctuationWindow_one_le {n k : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    1 ≤ fluctuationWindow n k := by
  apply Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have h := delta_lt_half hk
  linarith

theorem center_lower_of_auxiliary_probability {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k)
    (hprob : concentrationError n k < auxiliaryProbability n k ⌊c * n⌋₊) :
    c - 2 * densityWindow n k < center n k := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hf := Nat.floor_le (mul_nonneg hc0 hn'.le)
  have hm : ⌊c * (n : ℝ)⌋₊ ≤ mainCap n k := by
    have h := hf.trans (mul_le_mul_of_nonneg_right hcL hn'.le)
    exact_mod_cast (show (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ (mainCap n k : ℝ) by
      simpa only [mainCap, Nat.cast_mul] using h)
  by_contra h
  have hw := fluctuationWindow_one_le (n := n) hk hn0
  have he := fluctuationWindow_eq_mul (k := k) hn0
  have hc : center n k + 2 * densityWindow n k ≤ c := by linarith
  have hmul := mul_le_mul_of_nonneg_left hc hn'.le
  have hfloor := Nat.lt_floor_add_one (c * (n : ℝ))
  have hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ ⌊c * (n : ℝ)⌋₊ := by
    nlinarith
  exact not_lt_of_ge (auxiliaryProbability_center_upper hk hn hm hgap) hprob

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability := @_root_.OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability
