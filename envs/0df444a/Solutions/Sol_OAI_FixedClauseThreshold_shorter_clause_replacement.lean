-- Prove2me | solution 1 for OAI.FixedClauseThreshold.shorter_clause_replacement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:23:21.478449+00:00
-- url     : https://prove2.me/submissions/751953d6-ed79-459b-bf4f-1adcfd203df6

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Replacement.lean:L324-L374
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.shorter_clause_replacement. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Theorems.Thm_OAI_FixedClauseThreshold_replacement_numeric

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

theorem uniformProbability_true {α : Type*} [Fintype α] [Nonempty α] :
    uniformProbability (fun _ : α => True) = 1 := by
  classical
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial))]
  rw [Nat.card_eq_fintype_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

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

theorem uniformProbability_exists {α : Type*} [Fintype α] [Nonempty α]
    (p : α → Prop) (m : ℕ) :
    uniformProbability (fun f : Fin m → α => ∃ i, p (f i)) =
      1 - (1 - uniformProbability p) ^ m := by
  calc
    _ = uniformProbability (fun f : Fin m → α => ¬ ∀ i, ¬ p (f i)) :=
      uniformProbability_congr (fun _ => by simp)
    _ = 1 - uniformProbability (fun f : Fin m → α => ∀ i, ¬ p (f i)) :=
      uniformProbability_not _
    _ = _ := by rw [uniformProbability_forall (fun a => ¬ p a) m, uniformProbability_not]

theorem blockUNSAT_lower {n k g : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    1 - (1 - uniformProbability (fun C : ProperClause n k => KillsSolutions S C)) ^ g ≤
      blockUNSATProbability k g S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [← uniformProbability_exists]
  apply uniformProbability_mono
  rintro F ⟨i, hi⟩ ⟨σ, hσ, hs⟩
  exact hi σ hσ (hs i)

theorem replacementScale_pos {n k : ℕ} (hn : 0 < n) :
    0 < replacementScale n k := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem replacementScale_pow {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    replacementScale n k ^ k = (n : ℝ) := by
  unfold replacementScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  rw [one_div_mul_cancel hk', Real.rpow_one]

theorem replacementScale_one_le {n k : ℕ} (hn : 1 ≤ n) :
    1 ≤ replacementScale n k := by
  unfold replacementScale
  exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

theorem replacementError_small {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    1 / (n : ℝ) ≤ replacementError n k := by
  have ha := replacementScale_pos (k := k) hn
  have hpow : replacementScale n k ^ (k - 1) ≤ (n : ℝ) := by
    calc
      replacementScale n k ^ (k - 1) ≤ replacementScale n k ^ k :=
        pow_le_pow_right₀ (replacementScale_one_le (Nat.succ_le_of_lt hn)) (Nat.sub_le _ _)
      _ = _ := replacementScale_pow hn hk
  unfold replacementError
  rw [inv_pow, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hpow

theorem shorter_clause_replacement {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    uniformProbability (fun Q : ProperClause (n - 1) (k - 1) => KillsSolutions S Q) -
      replacementError n k ≤ blockUNSATProbability k (replacementBlock n k) S := by
  have hkn : k ≤ n - 1 := by omega
  let : Nonempty (ProperClause (n - 1) k) := nonempty_properClause hkn
  have heps : 0 ≤ replacementError n k :=
    pow_nonneg (inv_nonneg.mpr (replacementScale_pos (k := k) (by omega)).le) _
  by_cases hS : S.Nonempty
  · have hkill (r : ℕ) :
        uniformProbability (fun Q : ProperClause (n - 1) r => KillsSolutions S Q) =
          killFraction (forcedVariables S).card (n - 1) r := by
      unfold killFraction
      rw [← killingProbability_of_nonempty S hS]
      exact (uniformProbability_congr (fun _ => by simp [hS])).symm
    rw [hkill]
    apply le_trans _ (blockUNSAT_lower hkn S)
    rw [hkill]
    have hb : (forcedVariables S).card ≤ n - 1 := by
      simpa using Finset.card_le_univ (forcedVariables S)
    have hg : 2 * ((k - 1 : ℕ) + 1 : ℝ) * replacementScale n k ≤
        (replacementBlock n k : ℝ) := by
      have he : ((k - 1 : ℕ) : ℝ) + 1 = k := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ k))
      rw [he]
      exact Nat.le_ceil _
    have hsmall : 1 / ((n - 1 : ℕ) + 1 : ℝ) ≤ (replacementScale n k)⁻¹ ^ (k - 1) := by
      have he : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n))
      rw [he]
      exact replacementError_small (by omega) (by omega)
    have hrep := replacement_numeric (r := k - 1) (b := (forcedVariables S).card)
      (v := n - 1) (g := replacementBlock n k) (a := replacementScale n k)
      (by omega) (by omega) hb (replacementScale_pos (by omega)) hsmall hg
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k), replacementError] using hrep
  · have hSe : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    have hb : blockUNSATProbability k (replacementBlock n k)
        (∅ : Finset (Assignment (n - 1))) = 1 := by
      unfold blockUNSATProbability
      have hf : (fun F : Formula (n - 1) k (replacementBlock n k) =>
          ¬ ∃ σ ∈ (∅ : Finset (Assignment (n - 1))), Satisfies σ F) =
          (fun _ => True) := by
        funext F
        simp
      rw [hf]
      exact uniformProbability_true
    rw [hb]
    have hu := uniformProbability_le_one
      (fun Q : ProperClause (n - 1) (k - 1) => KillsSolutions ∅ Q)
    linarith

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.shorter_clause_replacement := @_root_.OAI.FixedClauseThreshold.shorter_clause_replacement
