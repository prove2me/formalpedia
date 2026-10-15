-- Prove2me | solution 1 for OAI.FixedClauseThreshold.center_bounds_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:38:28.385755+00:00
-- url     : https://prove2.me/submissions/ab9fc4c7-dff4-4269-8eee-80d0790c8b66

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterBounds.lean:L504-L517
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.center_bounds_eventually. The node keeps its source
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
import Theorems.Thm_OAI_FixedClauseThreshold_deficiency_union_bound
import Theorems.Thm_OAI_FixedClauseThreshold_properSATProbability_eq_survival
import Theorems.Thm_OAI_FixedClauseThreshold_uniformProbability_exists_le

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

theorem forcedVariables_eq_frozen {n : ℕ} {S : Finset (Assignment n)}
    {σ₀ : Assignment n} (hσ₀ : σ₀ ∈ S) :
    forcedVariables S = frozenCoordinates S σ₀ := by
  ext i
  simp only [forcedVariables, frozenCoordinates, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, b, hb⟩ σ hσ
    exact (hb σ hσ).trans (hb σ₀ hσ₀).symm
  · intro h
    exact ⟨⟨σ₀, hσ₀⟩, σ₀ i, h⟩

theorem card_killingClauses {n k : ℕ} (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    Fintype.card {C : ProperClause n k // KillsSolutions S C} =
      (forcedVariables S).card.choose k := by
  obtain ⟨σ₀, hσ₀⟩ := hS
  rw [Fintype.card_congr (killingClauseEquiv S σ₀ hσ₀),
    Fintype.card_coe, Finset.card_powersetCard, forcedVariables_eq_frozen hσ₀]

theorem killingProbability_of_nonempty {n k : ℕ} (S : Finset (Assignment n))
    (hS : S.Nonempty) :
    killingProbability k S = ((forcedVariables S).card.choose k : ℝ) /
      ((n.choose k : ℝ) * 2 ^ k) := by
  classical
  unfold killingProbability uniformProbability
  simp only [hS, true_and, card_killingClauses S hS, card_properClause,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

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

theorem uniformProbability_forall {α : Type*} [Fintype α] (p : α → Prop) (m : ℕ) :
    uniformProbability (fun f : Fin m → α => ∀ i, p (f i)) = uniformProbability p ^ m := by
  unfold uniformProbability
  have hc : Fintype.card {f : Fin m → α // ∀ i, p (f i)} =
      Fintype.card (Fin m → {a : α // p a}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ : Fin m => p))
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    div_pow]

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

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

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

theorem alive_le_one {n : ℕ} (S : Finset (Assignment n)) : alive S ≤ 1 := by
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

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.CenterBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem randomClause_satisfies {n k : ℕ} (hkn : k ≤ n) (σ : Assignment n) :
    uniformProbability (fun C : ProperClause n k => SatisfiesClause σ C) = 1 - (2 : ℝ)⁻¹ ^ k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := killingProbability_of_nonempty (k := k) {σ} (Finset.singleton_nonempty σ)
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hp : killingProbability k {σ} =
      uniformProbability (fun C : ProperClause n k => ¬SatisfiesClause σ C) := by
    apply uniformProbability_congr
    intro C
    simp [KillsSolutions]
  rw [hp, uniformProbability_not, forcedVariables_singleton, Finset.card_univ, Fintype.card_fin] at h
  have hr : (n.choose k : ℝ) / ((n.choose k : ℝ) * 2^k) = (2 : ℝ)⁻¹ ^ k := by
    rw [inv_pow]
    field_simp
  rw [hr] at h
  linarith

theorem first_moment_bound {n k m : ℕ} (hkn : k ≤ n) :
    properSATProbability n k m ≤ (2 : ℝ)^n * (1 - (2 : ℝ)⁻¹ ^ k)^m := by
  change uniformProbability (fun F : Formula n k m => ∃ σ, Satisfies σ F) ≤ _
  have h := uniformProbability_exists_le (fun F : Formula n k m => fun σ => Satisfies σ F)
  have hσ (σ : Assignment n) :
      uniformProbability (fun F : Formula n k m => Satisfies σ F) =
        (1 - (2 : ℝ)⁻¹ ^ k)^m := by
    change uniformProbability (fun F : Formula n k m => ∀ j, SatisfiesClause σ (F j)) = _
    rw [uniformProbability_forall, randomClause_satisfies hkn]
  simp only [hσ, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

theorem uniformMean_lower_tail {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) {t : ℝ} (_ht : 0 ≤ t) :
    t * uniformProbability (fun a => t ≤ f a) ≤ uniformMean f := by
  rw [uniformProbability_eq_mean, ← uniformMean_const_mul]
  apply uniformMean_mono
  intro a
  by_cases h : t ≤ f a
  · simpa only [ite_eq_left h, mul_one] using h
  · simpa only [ite_eq_right h, mul_zero] using hf a

theorem uniformMean_upper_cutoff {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {M t : ℝ} (hf : ∀ a, f a ≤ M) (ht : 0 ≤ t) :
    uniformMean f ≤ t + M * uniformProbability (fun a => t ≤ f a) := by
  calc
    _ ≤ uniformMean (fun a => t + M * if t ≤ f a then (1 : ℝ) else 0) := by
      apply uniformMean_mono
      intro a
      by_cases h : t ≤ f a
      · simp only [ite_eq_left h, mul_one]
        linarith [hf a]
      · simp only [ite_eq_right h, mul_zero, add_zero]
        exact le_of_not_ge h
    _ = _ := by rw [uniformMean_add, uniformMean_const, uniformMean_const_mul,
      ← uniformProbability_eq_mean]

theorem center_lower_by_probability {n k m : ℕ} (hkn : k ≤ n) (hm : m ≤ mainCap n k) :
    (m : ℝ) / n * properSATProbability n k m ≤ center n k := by
  have h := uniformMean_lower_tail (lifetime k (mainCap n k) (Finset.univ : Finset (Assignment n)))
    (fun F => lifetime_nonneg _ F) (show 0 ≤ (m : ℝ) by positivity)
  rw [← properSATProbability_eq_lifetime_tail hkn hm] at h
  unfold center lifetimeMean
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [div_mul_eq_mul_div] using hh

theorem center_upper_by_probability {n k m : ℕ} (hkn : k ≤ n) (hn : 0 < n)
    (hm : m ≤ mainCap n k) :
    center n k ≤ (m : ℝ) / n + capMultiplier k * properSATProbability n k m := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := uniformMean_upper_cutoff (lifetime k (mainCap n k) (Finset.univ : Finset (Assignment n)))
    (fun F => lifetime_le _ F) (show 0 ≤ (m : ℝ) by positivity)
  rw [← properSATProbability_eq_lifetime_tail hkn hm] at h
  unfold center lifetimeMean
  have hh := div_le_div_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  apply hh.trans_eq
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [mainCap, Nat.cast_mul]
  field_simp

theorem firstMomentBase_nonneg : 0 ≤ firstMomentBase := by
  unfold firstMomentBase
  positivity

theorem firstMomentBase_lt_one : firstMomentBase < 1 := by
  rw [firstMomentBase, Real.exp_neg]
  have h : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  exact (mul_inv_lt_iff₀ (Real.exp_pos 1)).mpr (by simpa using h)

theorem first_moment_linear {n k : ℕ} (hkn : k ≤ n) :
    properSATProbability n k (2^k * n) ≤ firstMomentBase^n := by
  apply (first_moment_bound hkn).trans
  have hq : 0 ≤ 1 - (2 : ℝ)⁻¹^k := by
    have := pow_le_one₀ (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1) (n := k)
    linarith
  have hp := pow_le_pow_left₀ hq (Real.one_sub_le_exp_neg ((2 : ℝ)⁻¹^k)) (2^k * n)
  have he : Real.exp (-((2 : ℝ)⁻¹^k))^(2^k * n) = Real.exp (-1)^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [inv_pow]
    have hk : (2 : ℝ)^k ≠ 0 := by positivity
    field_simp
  rw [he] at hp
  simpa only [firstMomentBase, mul_pow] using mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ 2^n)

theorem center_first_moment {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    center n k ≤ (2 : ℝ)^k + capMultiplier k * firstMomentBase^n := by
  have hm : 2^k * n ≤ mainCap n k := by
    dsimp [mainCap, capMultiplier]
    gcongr <;> omega
  have h := center_upper_by_probability hkn hn hm
  have he : ((2^k * n : ℕ) : ℝ) / n = (2 : ℝ)^k := by
    push_cast
    exact mul_div_cancel_right₀ _ (by exact_mod_cast Nat.ne_of_gt hn)
  rw [he] at h
  exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_left (first_moment_linear hkn)
    (Nat.cast_nonneg (capMultiplier k) : (0 : ℝ) ≤ capMultiplier k)) _)

theorem choose_exp_bound (N t : ℕ) (ht : 0 < t) :
    (N.choose t : ℝ) ≤ (Real.exp 1 * N / t)^t := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hf0 : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  have he : (t : ℝ)^t / t.factorial ≤ (Real.exp 1)^t := by
    have h := Real.pow_div_factorial_le_exp (x := (t : ℝ)) (Nat.cast_nonneg t) t
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hinv : (t.factorial : ℝ)⁻¹ ≤ (Real.exp 1 / t)^t := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos ht0 t)).mpr
    simpa only [div_eq_mul_inv, mul_comm] using he
  calc
    (N.choose t : ℝ) ≤ (N : ℝ)^t / t.factorial := Nat.choose_le_pow_div t N
    _ ≤ (N : ℝ)^t * (Real.exp 1 / t)^t := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

theorem smallDensity_pos : 0 < smallDensity := by unfold smallDensity; positivity

theorem smallDensity_le_one : smallDensity ≤ 1 := by
  unfold smallDensity
  have : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  linarith

theorem smallDensity_calibration : Real.exp 1 ^ 2 * smallDensity = 1 / 4 := by
  unfold smallDensity
  rw [← Real.exp_nat_mul]
  norm_num
  rw [← mul_div_assoc, ← Real.exp_add]
  norm_num

theorem hall_summand_bound {n k m t : ℕ} (hk : 3 ≤ k) (hn : 0 < n) (ht : 0 < t)
    (htn : t ≤ n) (hm : (m : ℝ) ≤ smallDensity * n) :
    (m.choose t : ℝ) * n.choose t * ((t : ℝ) / n)^(k * t) ≤
      (1 / n : ℝ) * (1 / 2 : ℝ)^t := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hr0 : 0 ≤ (t : ℝ) / n := by positivity
  have hr1 : (t : ℝ) / n ≤ 1 := (div_le_one hn0).mpr (by exact_mod_cast htn)
  have hc : (m.choose t : ℝ) * n.choose t * ((t : ℝ) / n)^(k * t) ≤
      ((1 / 4 : ℝ) * ((t : ℝ) / n))^t := by
    calc
      _ ≤ (Real.exp 1 * m / t)^t * (Real.exp 1 * n / t)^t *
          ((t : ℝ) / n)^(3 * t) := by
        apply mul_le_mul
        · exact mul_le_mul (choose_exp_bound m t ht) (choose_exp_bound n t ht)
            (Nat.cast_nonneg _) (by positivity)
        · exact pow_le_pow_of_le_one hr0 hr1 (Nat.mul_le_mul_right t hk)
        · positivity
        · positivity
      _ = (Real.exp 1 ^ 2 * (m / n) * ((t : ℝ) / n))^t := by
        rw [pow_mul, ← mul_pow, ← mul_pow]
        congr 1
        field_simp
      _ ≤ (Real.exp 1 ^ 2 * smallDensity * ((t : ℝ) / n))^t := by
        apply pow_le_pow_left₀ (by positivity)
        gcongr
        exact (div_le_iff₀ hn0).mpr hm
      _ = _ := by rw [smallDensity_calibration]
  apply hc.trans
  calc
    ((1 / 4 : ℝ) * ((t : ℝ) / n))^t = (1 / 4 : ℝ)^t * ((t : ℝ) / n)^t := mul_pow _ _ _
    _ ≤ (1 / 4 : ℝ)^t * ((t : ℝ) / n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [pow_one] using pow_le_pow_of_le_one hr0 hr1 ht
    _ ≤ (1 / 4 : ℝ)^t * ((2 : ℝ)^t / n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.lt_two_pow_self (n := t)).le) hn0.le
    _ = (1 / n : ℝ) * (1 / 2 : ℝ)^t := by
      rw [← mul_div_assoc, ← mul_pow]
      norm_num
      ring

theorem half_geometric_sum_le (m : ℕ) : ∑ t ∈ Finset.range m, (1 / 2 : ℝ)^(t+1) ≤ 1 := by
  have h := geom_sum_mul (1 / 2 : ℝ) m
  have he : ∑ t ∈ Finset.range m, (1 / 2 : ℝ)^(t+1) =
      (∑ t ∈ Finset.range m, (1 / 2 : ℝ)^t) * (1 / 2) := by
    simp_rw [pow_succ]
    rw [Finset.sum_mul]
  rw [he]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m]

theorem small_density_probability_bound {n k m : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n)
    (hm : (m : ℝ) ≤ smallDensity * n) :
    1 - (1 / n : ℝ) ≤ properSATProbability n k m := by
  have hn : 0 < n := by omega
  have hmn : m ≤ n := by
    have h := mul_le_mul_of_nonneg_right smallDensity_le_one (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    exact_mod_cast (show (m : ℝ) ≤ n from hm.trans (by simpa using h))
  have h := deficiency_union_bound hkn hn hmn
  have hs : (∑ t ∈ Finset.range m, (m.choose (t + 1) : ℝ) * n.choose (t + 1) *
      (((t + 1 : ℕ) : ℝ) / n)^(k * (t + 1))) ≤ 1 / n := by
    calc
      _ ≤ ∑ t ∈ Finset.range m, (1 / n : ℝ) * (1 / 2 : ℝ)^(t+1) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hall_summand_bound hk hn (by omega) (by have := Finset.mem_range.mp ht; omega) hm
      _ = (1 / n : ℝ) * ∑ t ∈ Finset.range m, (1 / 2 : ℝ)^(t+1) := (Finset.mul_sum ..).symm
      _ ≤ 1 / n := by
        simpa using mul_le_mul_of_nonneg_left (half_geometric_sum_le m) (by positivity : (0 : ℝ) ≤ 1/n)
  linarith

theorem center_lower_explicit {n k : ℕ} (hk : 3 ≤ k) (hkn : k ≤ n)
    (hn : 2 ≤ n) (hlarge : 2 ≤ smallDensity * n) : lowerCenterBound ≤ center n k := by
  let m : ℕ := ⌊smallDensity * n⌋₊
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm : (m : ℝ) ≤ smallDensity * n := Nat.floor_le (by positivity)
  have hmn : m ≤ n := by
    have h := mul_le_mul_of_nonneg_right smallDensity_le_one hn0.le
    exact_mod_cast (show (m : ℝ) ≤ n from hm.trans (by simpa using h))
  have hmcap : m ≤ mainCap n k := hmn.trans (by
    unfold mainCap
    exact Nat.le_mul_of_pos_left _ (by unfold capMultiplier; positivity))
  have hprob := small_density_probability_bound hk hkn hm
  have hinv : (1 / n : ℝ) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast hn
  have hhalf : (1 / 2 : ℝ) ≤ properSATProbability n k m := by linarith
  have hfloor : smallDensity * n < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hratio : smallDensity / 2 ≤ (m : ℝ) / n := by
    apply (le_div_iff₀ hn0).mpr
    nlinarith
  have hl := center_lower_by_probability hkn hmcap
  have hmul := mul_le_mul hratio hhalf (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (div_nonneg (Nat.cast_nonneg m) hn0.le)
  unfold lowerCenterBound
  nlinarith

theorem center_bounds_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in Filter.atTop, lowerCenterBound ≤ center n k ∧ center n k ≤ (2 : ℝ)^k + 1 := by
  have hlin : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ smallDensity * n := by
    have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop smallDensity_pos
    exact ht.eventually (Filter.eventually_ge_atTop 2)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one firstMomentBase_nonneg firstMomentBase_lt_one
  have ht : Filter.Tendsto (fun n : ℕ => (capMultiplier k : ℝ) * firstMomentBase^n)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hpow.const_mul (capMultiplier k : ℝ)
  have hu := ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hn : ∀ᶠ n : ℕ in Filter.atTop, k + 1 ≤ n := Filter.eventually_ge_atTop _
  filter_upwards [hlin, hu, hn] with n hlarge hu hn
  exact ⟨center_lower_explicit hk (by omega) (by omega) hlarge,
    (center_first_moment (by omega) (by omega)).trans (by linarith)⟩

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.center_bounds_eventually := @_root_.OAI.FixedClauseThreshold.center_bounds_eventually
