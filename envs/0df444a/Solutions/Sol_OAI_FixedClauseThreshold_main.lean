-- Prove2me | solution 1 for OAI.FixedClauseThreshold.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T06:02:55.261807+00:00
-- url     : https://prove2.me/submissions/d1d3a2bd-7bdd-4ed6-be1d-6cb66d2733bc

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Main.lean:L122-L127
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.FixedClauseThreshold.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_FixedClauseThreshold_main) verbatim and is proved by it.
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
import Definitions.Def_OAI_Probability_RandomSAT_Convergence
import Definitions.Def_OAI_Probability_RandomSAT_Main
import Theorems.Thm_OAI_FixedClauseThreshold_center_bounds_eventually
import Theorems.Thm_OAI_FixedClauseThreshold_center_tendsto
import Theorems.Thm_OAI_FixedClauseThreshold_concentration_capped
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

theorem properSATProbability_nonneg (n k m : ℕ) :
    0 ≤ properSATProbability n k m := by
  unfold properSATProbability
  positivity

theorem properSATProbability_le_one (n k m : ℕ) :
    properSATProbability n k m ≤ 1 := by
  classical
  unfold properSATProbability
  by_cases h : Fintype.card (Formula n k m) = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Fintype.card_subtype_le (fun F : Formula n k m => Satisfiable F)

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

theorem uniformProbability_not {α : Type*} [Fintype α] [Nonempty α] (p : α → Prop) :
    uniformProbability (fun a => ¬ p a) = 1 - uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le p), sub_div,
    div_self (by exact_mod_cast Fintype.card_ne_zero)]

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
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

theorem alive_mono {n : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T) :
    alive S ≤ alive T := by
  unfold alive
  by_cases hS : S.Nonempty
  · have hT := hS.mono hST
    simp [hS, hT]
  · simp only [ite_eq_right hS]
    split <;> norm_num

theorem survival_mono_solutions {n k m : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T) :
    survival k m S ≤ survival k m T := by
  rw [survival_eq_mean, survival_eq_mean]
  apply uniformMean_mono
  intro F
  apply alive_mono
  intro σ hσ
  rw [mem_restrictSolutions] at hσ ⊢
  exact ⟨hST hσ.1, hσ.2⟩

theorem survival_antitone {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    Antitone (fun m => survival k m S) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  apply antitone_nat_of_succ_le
  intro m
  rw [survival_succ, ← uniformMean_const (α := ProperClause n k) (survival k m S)]
  apply uniformMean_mono
  intro C
  exact survival_mono_solutions (Finset.filter_subset _ _)

theorem properSATProbability_antitone {n k : ℕ} (hkn : k ≤ n) :
    Antitone (properSATProbability n k) := by
  intro i j hij
  rw [properSATProbability_eq_survival, properSATProbability_eq_survival]
  exact survival_antitone hkn _ hij

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

theorem properSATProbability_center_upper {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (n : ℝ) * center n k + fluctuationWindow n k ≤ m) :
    properSATProbability n k m ≤ concentrationError n k := by
  rw [properSATProbability_eq_lifetime_tail (by omega) hm]
  apply (uniformProbability_mono (fun F hF => ?_)).trans (concentration_capped hk hn)
  exact le_trans (by linarith) (le_abs_self _)

theorem properSATProbability_center_lower {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hm : m ≤ mainCap n k)
    (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
    1 - concentrationError n k ≤ properSATProbability n k m := by
  let : Nonempty (ProperClause n k) := nonempty_properClause (by omega)
  rw [properSATProbability_eq_lifetime_tail (by omega) hm]
  have h := uniformProbability_mono (p := fun F : Formula n k (mainCap n k) =>
    ¬ (m : ℝ) ≤ lifetime k (mainCap n k) Finset.univ F)
    (q := fun F => fluctuationWindow n k ≤
      |lifetime k (mainCap n k) Finset.univ F - (n : ℝ) * center n k|) (fun F hF => by
        have hh : lifetime k (mainCap n k) Finset.univ F < m := lt_of_not_ge hF
        exact le_trans (by linarith) (neg_le_abs _))
  rw [uniformProbability_not] at h
  linarith [concentration_capped hk hn]

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

theorem densityWindow_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => densityWindow n k) Filter.atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop (delta_pos hk)).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem concentrationError_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => concentrationError n k) Filter.atTop (nhds 0) := by
  have hη : 0 < eta k := by rw [eta_eq_twice_delta]; positivity [delta_pos hk]
  have ht := (tendsto_rpow_neg_atTop hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [concentrationError, Function.comp_apply, mul_zero] using ht.const_mul (varianceConstant k)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Main ----
namespace OAI

/-!
For every fixed clause size at least three, the proper-clause satisfiability
probability has a positive finite limiting threshold. No conclusion is asserted
at the critical density.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem limitingCenter_bounds (k : ℕ) (hk : 3 ≤ k) :
    lowerCenterBound ≤ limitingCenter k ∧ limitingCenter k ≤ (2 : ℝ)^k + 1 := by
  have ht := center_tendsto k hk
  have hb := center_bounds_eventually k hk
  exact ⟨ge_of_tendsto ht (hb.mono (fun _ h => h.1)), le_of_tendsto ht (hb.mono (fun _ h => h.2))⟩

theorem limitingCenter_pos (k : ℕ) (hk : 3 ≤ k) : 0 < limitingCenter k :=
  lowerCenterBound_pos.trans_le (limitingCenter_bounds k hk).1

theorem limitingCenter_lt_cap (k : ℕ) (hk : 3 ≤ k) : limitingCenter k < capMultiplier k := by
  have hp : (1 : ℝ) < 2^k := one_lt_pow₀ (by norm_num) (by omega : k ≠ 0)
  have he : (capMultiplier k : ℝ) = 2^k * 2 := by simp [capMultiplier, pow_succ]
  rw [he]
  have h := (limitingCenter_bounds k hk).2
  linarith

theorem floor_density_le_cap {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k) :
    ⌊c * (n : ℝ)⌋₊ ≤ mainCap n k := by
  have h := (Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))).trans
    (mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  exact_mod_cast (show (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ (mainCap n k : ℝ) by
    simpa only [mainCap, Nat.cast_mul] using h)

theorem subcritical_limit (k : ℕ) (hk : 3 ≤ k) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : c < limitingCenter k) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 1) := by
  have hcL : c ≤ capMultiplier k := (hc.trans (limitingCenter_lt_cap k hk)).le
  have hcenter : Filter.Tendsto (fun n : ℕ => center n k - densityWindow n k)
      Filter.atTop (nhds (limitingCenter k)) := by
    simpa only [sub_zero] using (center_tendsto k hk).sub (densityWindow_tendsto k hk)
  have hmargin := hcenter.eventually (Ioi_mem_nhds hc)
  have hlower : ∀ᶠ n : ℕ in Filter.atTop,
      1 - concentrationError n k ≤ properSATProbability n k ⌊c * (n : ℝ)⌋₊ := by
    filter_upwards [hmargin, Filter.eventually_ge_atTop (k + 1)] with n hmargin hn
    apply properSATProbability_center_lower hk hn (floor_density_le_cap hc0 hcL)
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [fluctuationWindow_eq_mul hn0]
    have hmul := mul_le_mul_of_nonneg_left hmargin.le hn'.le
    have hf := Nat.floor_le (mul_nonneg hc0 hn'.le)
    nlinarith
  have hlowT : Filter.Tendsto (fun n : ℕ => 1 - concentrationError n k) Filter.atTop (nhds 1) := by
    simpa only [sub_zero] using (concentrationError_tendsto k hk).const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowT tendsto_const_nhds hlower
    (Filter.Eventually.of_forall fun n => properSATProbability_le_one n k _)

theorem supercritical_limit_below_cap (k : ℕ) (hk : 3 ≤ k) (c : ℝ)
    (hc : limitingCenter k < c) (hcL : c ≤ capMultiplier k) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 0) := by
  have hc0 : 0 ≤ c := ((limitingCenter_pos k hk).trans hc).le
  have hd : Filter.Tendsto (fun n : ℕ => 2 * densityWindow n k) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (densityWindow_tendsto k hk).const_mul (2 : ℝ)
  have hcenter : Filter.Tendsto (fun n : ℕ => center n k + 2 * densityWindow n k)
      Filter.atTop (nhds (limitingCenter k)) := by
    simpa only [add_zero] using (center_tendsto k hk).add hd
  have hmargin := hcenter.eventually_lt_const hc
  have hupper : ∀ᶠ n : ℕ in Filter.atTop,
      properSATProbability n k ⌊c * (n : ℝ)⌋₊ ≤ concentrationError n k := by
    filter_upwards [hmargin, Filter.eventually_ge_atTop (k + 1)] with n hmargin hn
    apply properSATProbability_center_upper hk hn (floor_density_le_cap hc0 hcL)
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hw := fluctuationWindow_one_le (n := n) hk hn0
    have he := fluctuationWindow_eq_mul (k := k) hn0
    have hmul := mul_le_mul_of_nonneg_left hmargin.le hn'.le
    have hf := Nat.lt_floor_add_one (c * (n : ℝ))
    nlinarith
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => properSATProbability_nonneg n k _)
    hupper (concentrationError_tendsto k hk)

theorem supercritical_limit (k : ℕ) (hk : 3 ≤ k) (c : ℝ)
    (hc : limitingCenter k < c) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 0) := by
  let d := min c (capMultiplier k : ℝ)
  have hd : limitingCenter k < d := lt_min hc (limitingCenter_lt_cap k hk)
  have hdL : d ≤ capMultiplier k := min_le_right _ _
  have ht := supercritical_limit_below_cap k hk d hd hdL
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => properSATProbability_nonneg n k _) _ ht
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  apply properSATProbability_antitone hn
  exact Nat.floor_mono (mul_le_mul_of_nonneg_right (min_le_left c (capMultiplier k : ℝ)) (Nat.cast_nonneg n))

theorem main (k : ℕ) (hk : 3 ≤ k) : HasLimitingThreshold k := by
  refine ⟨limitingCenter k, limitingCenter_pos k hk, ?_, ?_⟩
  · intro c hc0 hc
    exact subcritical_limit k hk c hc0 hc
  · intro c hc
    exact supercritical_limit k hk c hc

end

end FixedClauseThreshold

end OAI

-- ---- mission target ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem solution (k : ℕ) (hk : 3 ≤ k) : HasLimitingThreshold k := by
  first
    | exact OAI.FixedClauseThreshold.main k hk
    | exact OAI.FixedClauseThreshold.main
    | (apply OAI.FixedClauseThreshold.main <;> assumption)
    | (intros; apply OAI.FixedClauseThreshold.main <;> assumption)
