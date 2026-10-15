-- Prove2me | solution 1 for OAI.FixedClauseThreshold.auxiliaryProbability_center_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:46:34.067565+00:00
-- url     : https://prove2.me/submissions/4962b848-fb55-4116-aa37-179625ffd7ab

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Transfer.lean:L300-L319
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.auxiliaryProbability_center_lower. The node keeps its source
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
import Theorems.Thm_OAI_FixedClauseThreshold_clauseAverage_alive
import Theorems.Thm_OAI_FixedClauseThreshold_concentration_capped
import Theorems.Thm_OAI_FixedClauseThreshold_embeddedAverage_alive
import Theorems.Thm_OAI_FixedClauseThreshold_finiteClauseAverage_commute
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

theorem uniformProbability_le_one {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p ≤ 1 := by
  classical
  unfold uniformProbability
  by_cases h : Fintype.card α = 0
  · simp [h]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr
    exact_mod_cast Fintype.card_subtype_le p

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

theorem fluctuationWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < fluctuationWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem center_le_capMultiplier {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    center n k ≤ capMultiplier k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  have h := uniformMean_mono (fun F : Formula n k (mainCap n k) => lifetime_le Finset.univ F)
  rw [uniformMean_const] at h
  unfold center lifetimeMean
  rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)]
  simpa [mainCap] using h

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

theorem finiteClauseAverage_const_mul {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    finiteClauseAverage sat (fun S => c * f S) = (fun S => c * finiteClauseAverage sat f S) := by
  funext S
  exact uniformMean_const_mul _ _

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

theorem card_injective_lists (n k : ℕ) :
    Fintype.card {f : Fin k → Fin n // Function.Injective f} = n.descFactorial k := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin n)),
    Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]

theorem properFraction_probability (n k : ℕ) :
    properFraction n k = uniformProbability (fun f : Fin k → Fin n => Function.Injective f) := by
  unfold properFraction uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  simp only [Nat.card_eq_fintype_card, card_injective_lists, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow]

theorem properFraction_nonneg (n k : ℕ) : 0 ≤ properFraction n k := by
  unfold properFraction
  positivity

theorem properFraction_le_one (n k : ℕ) : properFraction n k ≤ 1 := by
  rw [properFraction_probability]
  exact uniformProbability_le_one _

theorem repetition_count_mono {b n k : ℕ} (hbn : b ≤ n) :
    (b : ℝ)^k - b.descFactorial k ≤ (n : ℝ)^k - n.descFactorial k := by
  let e : {f : Fin k → Fin b // ¬ Function.Injective f} ↪
      {f : Fin k → Fin n // ¬ Function.Injective f} := {
    toFun := fun f => ⟨fun i => Fin.castLE hbn (f.val i), by
      intro hinj
      apply f.property
      intro i j hij
      apply hinj
      exact congrArg (Fin.castLE hbn) hij⟩
    inj' := by
      intro f g h
      apply Subtype.ext
      funext i
      apply Fin.castLE_injective hbn
      exact congrFun (congrArg Subtype.val h) i }
  have h := Fintype.card_le_of_embedding e
  have hf (v : ℕ) : Fintype.card {f : Fin k → Fin v // ¬ Function.Injective f} =
      v^k - v.descFactorial k := by
    simp only [Fintype.card_subtype_compl, card_injective_lists, Fintype.card_fun, Fintype.card_fin]
  have hd (v : ℕ) : v.descFactorial k ≤ v^k := by
    have h := Fintype.card_subtype_le (fun f : Fin k → Fin v => Function.Injective f)
    simpa only [card_injective_lists, Fintype.card_fun, Fintype.card_fin] using h
  rw [hf, hf] at h
  have h' := (Nat.cast_le (α := ℝ)).mpr h
  simpa only [Nat.cast_sub (hd _), Nat.cast_pow] using h'

theorem properFraction_mul_kill {b n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    properFraction n k * killFraction b n k =
      (b.descFactorial k : ℝ) / ((2 : ℝ)^k * (n : ℝ)^k) := by
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hkn)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold properFraction killFraction
  rw [Nat.descFactorial_eq_factorial_mul_choose n k, Nat.descFactorial_eq_factorial_mul_choose b k]
  push_cast
  field_simp

theorem auxiliary_kill_le_repetition {b n k : ℕ} (hbn : b ≤ n) (hkn : k ≤ n)
    (hn : 0 < n) :
    ((b : ℝ) / (2 * n))^k ≤ 1 - properFraction n k +
      properFraction n k * killFraction b n k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcount := repetition_count_mono (k := k) hbn
  have hq := properFraction_le_one n k
  have hden : (0 : ℝ) < (2 : ℝ)^k * (n : ℝ)^k := by positivity
  have hp : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  rw [properFraction_mul_kill hkn hn]
  unfold properFraction at hq ⊢
  rw [div_le_one (by positivity)] at hq
  rw [div_pow, mul_pow]
  have hnonneg : 0 ≤ (n : ℝ)^k - n.descFactorial k := sub_nonneg.mpr hq
  have hm := mul_le_mul_of_nonneg_right hp hnonneg
  have hd : (b : ℝ)^k - b.descFactorial k ≤
      (2 : ℝ)^k * ((n : ℝ)^k - n.descFactorial k) := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hd hden.le
  have he : (2 : ℝ)^k * ((n : ℝ)^k - n.descFactorial k) /
      ((2 : ℝ)^k * (n : ℝ)^k) = 1 - (n.descFactorial k : ℝ) / (n : ℝ)^k := by
    field_simp
  rw [he, sub_div] at hdiv
  linarith

theorem scaled_proper_le_auxiliaryAverage {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    (fun S => properFraction n k * clauseAverage k alive S) ≤ auxiliaryAverage (n := n) k alive := by
  intro S
  change properFraction n k * clauseAverage k alive S ≤ auxiliaryAverage k alive S
  rw [auxiliaryAverage_alive hn, clauseAverage_alive hkn]
  have hb : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := auxiliary_kill_le_repetition hb hkn hn
  have hh : properFraction n k * (1 - killFraction (forcedVariables S).card n k) ≤
      1 - (forcedFraction S / 2)^k := by
    unfold forcedFraction
    rw [div_div]
    rw [mul_comm (n : ℝ) 2]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hh (alive_nonneg S)
  nlinarith

theorem proper_scaled_le_auxiliaryProbability {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) (m : ℕ) :
    (properFraction n k)^m * properSATProbability n k m ≤ auxiliaryProbability n k m := by
  have hstep := scaled_proper_le_auxiliaryAverage hn hkn
  let B : (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
    fun f S => properFraction n k * clauseAverage k f S
  have hB : Monotone B := by
    intro f g h S
    exact mul_le_mul_of_nonneg_left (finiteClauseAverage_mono _ h S) (properFraction_nonneg n k)
  have hcomm : Function.Commute (auxiliaryAverage (n := n) k) B := by
    intro f
    unfold B auxiliaryAverage embeddedAverage
    rw [finiteClauseAverage_const_mul]
    funext S
    congr 1
    exact congrFun (finiteClauseAverage_commute
      (fun C : AuxiliaryClause n k => fun σ => auxiliarySatisfies σ (embedAuxiliaryClause id C))
      (fun C : ProperClause n k => fun σ => SatisfiesClause σ C) f) S
  have hit (j : ℕ) (f : Finset (Assignment n) → ℝ) :
      B^[j] f = (fun S => (properFraction n k)^j * (clauseAverage k)^[j] f S) := by
    induction j with
    | zero => funext S; simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      unfold B clauseAverage
      funext S
      rw [uniformMean_const_mul]
      rw [Function.iterate_succ_apply', pow_succ]
      ring
  have h := iterate_compare_of_commute (auxiliaryAverage k) B
    (fun _ _ h => finiteClauseAverage_mono _ h) hB hcomm hstep m Finset.univ
  rw [hit] at h
  rw [properSATProbability_eq_survival]
  exact h

theorem repeatPairs_succ (k : ℕ) : repeatPairs (k + 1) = repeatPairs k + k := by
  simp only [repeatPairs, Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add]
  ring

theorem repeatPairs_nonneg (k : ℕ) : 0 ≤ repeatPairs k := Nat.cast_nonneg _

theorem properFraction_succ {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    properFraction n (k + 1) = properFraction n k * (1 - (k : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold properFraction
  rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hkn, pow_succ]
  field_simp

theorem properFraction_lower {n k : ℕ} (hn : 0 < n) (hkn : k ≤ n) :
    1 - repeatPairs k / n ≤ properFraction n k := by
  induction k with
  | zero => simp [properFraction]
  | succ k ih =>
    have hkn' : k ≤ n := by omega
    have hi := ih hkn'
    have hle := properFraction_le_one n k
    have hprod := mul_le_mul_of_nonneg_right hle (show 0 ≤ (k : ℝ) / n by positivity)
    rw [properFraction_succ hn hkn', repeatPairs_succ, add_div]
    nlinarith

theorem exp_neg_two_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h := Real.add_one_le_exp (2 * x)
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ 1 - x by linarith)
  have hh : 1 ≤ Real.exp (2 * x) * (1 - x) := by nlinarith
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (2 * x))).mp
  rw [← Real.exp_add, show 2 * x + -2 * x = 0 by ring, Real.exp_zero]
  simpa only [mul_comm] using hh

theorem properFraction_pow_lower {n k m : ℕ} (hn : 0 < n) (hkn : k ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (hm : m ≤ mainCap n k) :
    transferFactor k ≤ (properFraction n k)^m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ repeatPairs k / n := div_nonneg (repeatPairs_nonneg k) hn'.le
  have hx : repeatPairs k / n ≤ 1 / 2 := (div_le_iff₀ hn').mpr (by linarith)
  have hbase := (exp_neg_two_le_one_sub hx0 hx).trans (properFraction_lower hn hkn)
  have hpow := pow_le_pow_left₀ (Real.exp_pos _).le hbase m
  rw [← Real.exp_nat_mul] at hpow
  apply le_trans _ hpow
  apply Real.exp_le_exp.mpr
  have hm' : (m : ℝ) ≤ (capMultiplier k : ℝ) * n := by exact_mod_cast hm
  have hh := mul_le_mul_of_nonneg_right hm' hx0
  have he : ((capMultiplier k : ℝ) * n) * (repeatPairs k / n) =
      (capMultiplier k : ℝ) * repeatPairs k := by field_simp
  rw [he] at hh
  nlinarith

theorem auxiliaryProbability_center_lower {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (hnrep : 2 * repeatPairs k ≤ n) (herror : concentrationError n k ≤ 1 / 2)
    (hgap : (m : ℝ) + fluctuationWindow n k ≤ (n : ℝ) * center n k) :
    transferLower k ≤ auxiliaryProbability n k m := by
  have hn0 : 0 < n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hcenter := center_le_capMultiplier (by omega : k ≤ n) hn0
  have hm : m ≤ mainCap n k := by
    have hw := (fluctuationWindow_pos (k := k) hn0).le
    have h := mul_le_mul_of_nonneg_left hcenter hn'.le
    have : (m : ℝ) ≤ (mainCap n k : ℝ) := by
      simp only [mainCap, Nat.cast_mul]
      nlinarith
    exact_mod_cast this
  have hprob := properSATProbability_center_lower hk hn hm hgap
  have hhalf : (1 / 2 : ℝ) ≤ properSATProbability n k m := by linarith
  have hmul := mul_le_mul (properFraction_pow_lower hn0 (by omega) hnrep hm) hhalf
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (properFraction_nonneg n k |> fun h => pow_nonneg h m)
  apply le_trans _ (proper_scaled_le_auxiliaryProbability hn0 (by omega) m)
  simpa only [transferLower, div_eq_mul_inv, one_mul] using hmul

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.auxiliaryProbability_center_lower := @_root_.OAI.FixedClauseThreshold.auxiliaryProbability_center_lower
