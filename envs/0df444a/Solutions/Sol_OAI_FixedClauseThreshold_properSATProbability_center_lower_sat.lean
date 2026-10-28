-- Prove2me | solution 1 for OAI.FixedClauseThreshold.properSATProbability_center_lower_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:45:33.127289+00:00
-- url     : https://prove2.me/submissions/e2658674-d9a8-4615-8514-637c9b43ec13

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A002

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Clauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem killingProbability_eq {n k : ℕ} (hk : 0 < k) (S : Finset (Assignment n)) :
    killingProbability k S = ((forcedVariables S).card.choose k : ℝ) /
      ((n.choose k : ℝ) * 2 ^ k) := by
  by_cases hS : S.Nonempty
  · exact killingProbability_of_nonempty S hS
  · have h : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [Nat.choose_eq_zero_of_lt hk]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Replacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Quantitative comparison of a shorter clause with a block of independent proper
clauses, uniformly over the background solution set.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem killFraction_nonneg (b n r : ℕ) : 0 ≤ killFraction b n r := by
  unfold killFraction
  positivity

theorem killFraction_succ {b n r : ℕ} (hrn : r + 1 ≤ n) :
    killFraction b n (r + 1) =
      killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by
  have hnc : (n.choose r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega : r ≤ n))
  have hncs : (n.choose (r + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hrn)
  have hnr : ((n - r : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : n - r ≠ 0)
  have hb : (b.choose (r + 1) : ℝ) * (r + 1) =
      (b.choose r : ℝ) * ((b - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq b r
  have hn : (n.choose (r + 1) : ℝ) * (r + 1) =
      (n.choose r : ℝ) * ((n - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n r
  unfold killFraction
  rw [pow_succ]
  field_simp
  nlinarith [congrArg (fun a : ℝ => a * (n.choose (r + 1) : ℝ)) hb,
    congrArg (fun a : ℝ => a * (b.choose (r + 1) : ℝ)) hn]

theorem sub_ratio_le {b n r : ℕ} (hbn : b ≤ n) (hrb : r ≤ b) (hrn : r < n) :
    ((b - r : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) ≤ (b : ℝ) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrn
  rw [div_le_div_iff₀ hnr hn, Nat.cast_sub hrb, Nat.cast_sub (Nat.le_of_lt hrn)]
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (sub_nonneg.mpr hbn')]

theorem killFraction_le_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ ((b : ℝ) / (2 * n)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    by_cases hbr : b < r + 1
    · simp only [killFraction, Nat.choose_eq_zero_of_lt hbr, Nat.cast_zero, zero_div]
      positivity
    · have hrb : r ≤ b := by omega
      have ih' := ih (by omega)
      rw [killFraction_succ hrn, pow_succ]
      have hratio := sub_ratio_le hbn hrb (by omega : r < n)
      have hhalf : ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) ≤
          (b : ℝ) / (2 * n) := by
        simpa only [div_mul_eq_div_div_swap] using div_le_div_of_nonneg_right hratio
          (by norm_num : (0 : ℝ) ≤ 2)
      calc
        killFraction b n r * ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) =
            killFraction b n r * (((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ))) := by ring
        _ ≤ ((b : ℝ) / (2 * n)) ^ r * ((b : ℝ) / (2 * n)) :=
          mul_le_mul ih' hhalf (by positivity) (by positivity)

theorem killFraction_le_half_pow {b n r : ℕ} (hbn : b ≤ n) (hrn : r ≤ n)
    (hn : 0 < n) : killFraction b n r ≤ (1 / 2 : ℝ) ^ r := by
  apply (killFraction_le_pow hbn hrn hn).trans
  apply pow_le_pow_left₀ (by positivity)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).mpr
  have hbn' : (b : ℝ) ≤ n := by exact_mod_cast hbn
  linarith

theorem nat_le_internal_choose {n r : ℕ} (hr : 1 ≤ r) (hrn : r < n) :
    n ≤ n.choose r := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
    cases r with
    | zero => omega
    | succ r =>
      by_cases h : r = 0
      · subst r
        simp
      · rw [Nat.choose_succ_succ]
        have hlow := ih (by omega : 1 ≤ r) (by omega : r < n)
        have hpos := Nat.choose_pos (by omega : r.succ ≤ n)
        omega

theorem killFraction_small_forcing {b n r : ℕ} (hr : 1 ≤ r) (hrn : r < n)
    (hbr : b ≤ r) : killFraction b n r ≤ 1 / (n + 1 : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnc : (n : ℝ) ≤ n.choose r := by exact_mod_cast nat_le_internal_choose hr hrn
  have hb : (b.choose r : ℝ) ≤ 1 := by
    exact_mod_cast (Nat.choose_le_choose r hbr).trans_eq (Nat.choose_self r)
  have hp : (2 : ℝ) ≤ 2 ^ r := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hncpos : (0 : ℝ) < n.choose r := by linarith
  have hden : (0 : ℝ) < (n.choose r : ℝ) * 2 ^ r := by positivity
  unfold killFraction
  apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ) < n + 1)).mpr
  nlinarith [mul_le_mul hnc hp (by positivity : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ n.choose r)]

theorem succ_ratio_lower {b n r : ℕ} (hrb : r + 1 ≤ b) (hrn : r < n) :
    (b : ℝ) / (2 * n * (r + 1)) ≤
      ((b - r : ℕ) : ℝ) / (2 * ((n - r : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnr : (0 : ℝ) < (n - r : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hrn
  have hrb' : (r + 1 : ℝ) ≤ b := by exact_mod_cast hrb
  have hr : (0 : ℝ) ≤ r := by positivity
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n * (r + 1))
    (by positivity : (0 : ℝ) < 2 * (n - r : ℕ))]
  rw [Nat.cast_sub (by omega : r ≤ b), Nat.cast_sub (Nat.le_of_lt hrn)]
  have haux : (b : ℝ) ≤ (b - r) * (r + 1) := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hrb')]
  nlinarith [mul_le_mul_of_nonneg_right haux hn.le,
    mul_nonneg (Nat.cast_nonneg b : (0 : ℝ) ≤ b) hr]

theorem killFraction_succ_lower {b n r : ℕ} (hrb : r + 1 ≤ b) (hrn : r < n) :
    killFraction b n r * ((b : ℝ) / (2 * n)) / (r + 1) ≤
      killFraction b n (r + 1) := by
  rw [killFraction_succ (by omega : r + 1 ≤ n)]
  have h := mul_le_mul_of_nonneg_left (succ_ratio_lower hrb hrn)
    (killFraction_nonneg b n r)
  simpa only [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

theorem power_survival_bound {q : ℝ} (_hq0 : 0 ≤ q) (hq1 : q ≤ 1) (g : ℕ) :
    (1 - q) ^ g * (1 + (g : ℝ) * q) ≤ 1 := by
  induction g with
  | zero => simp
  | succ g ih =>
    have hstep : (1 - q) * (1 + ((g : ℝ) + 1) * q) ≤ 1 + (g : ℝ) * q := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ g + 1) (sq_nonneg q)]
    calc
      (1 - q) ^ (g + 1) * (1 + ((g + 1 : ℕ) : ℝ) * q) =
          (1 - q) ^ g * ((1 - q) * (1 + ((g : ℝ) + 1) * q)) := by
            push_cast
            ring
      _ ≤ (1 - q) ^ g * (1 + (g : ℝ) * q) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (sub_nonneg.mpr hq1) _)
      _ ≤ 1 := ih

theorem block_ge_of_double {x q : ℝ} {g : ℕ}
    (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hg : 2 * x ≤ (g : ℝ) * q) : x ≤ 1 - (1 - q) ^ g := by
  have h := power_survival_bound hq0 hq1 g
  have hx1 : 0 ≤ 1 - x := by linarith
  have hg0 : 0 ≤ (g : ℝ) * q := by positivity
  have hh : 1 ≤ (1 - x) * (1 + (g : ℝ) * q) := by
    nlinarith [mul_le_mul_of_nonneg_right hg hx1, mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  have hb : (1 - q) ^ g ≤ 1 - x := by
    exact (mul_le_mul_iff_left₀ (by positivity : 0 < 1 + (g : ℝ) * q)).mp
      (by nlinarith)
  linarith

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

theorem replacement_numeric {b v r g : ℕ} {a : ℝ}
    (hr : 1 ≤ r) (hrv : r < v) (hbv : b ≤ v) (ha : 0 < a)
    (hsmall : 1 / (v + 1 : ℝ) ≤ a⁻¹ ^ r)
    (hg : 2 * (r + 1 : ℝ) * a ≤ (g : ℝ)) :
    killFraction b v r - a⁻¹ ^ r ≤ 1 - (1 - killFraction b v (r + 1)) ^ g := by
  let x := killFraction b v r
  let q := killFraction b v (r + 1)
  have hv : 0 < v := by omega
  have hx0 : 0 ≤ x := killFraction_nonneg _ _ _
  have hq0 : 0 ≤ q := killFraction_nonneg _ _ _
  have hxhalf : x ≤ 1 / 2 := by
    apply (killFraction_le_half_pow hbv (Nat.le_of_lt hrv) hv).trans
    calc
      (1 / 2 : ℝ) ^ r ≤ (1 / 2 : ℝ) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hr
      _ = 1 / 2 := by simp
  have hq1 : q ≤ 1 := by
    apply (killFraction_le_half_pow hbv (by omega) hv).trans
    exact pow_le_one₀ (by norm_num) (by norm_num)
  by_cases hx : x ≤ a⁻¹ ^ r
  · have hpow : (1 - q) ^ g ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr hq1) (by linarith)
    change x - a⁻¹ ^ r ≤ 1 - (1 - q) ^ g
    linarith
  · have hrb : r + 1 ≤ b := by
      by_contra h
      have hb : b ≤ r := by omega
      have hbound := killFraction_small_forcing hr hrv hb
      exact hx (hbound.trans hsmall)
    have ht : a⁻¹ ≤ (b : ℝ) / (2 * v) := by
      by_contra h
      have hle : (b : ℝ) / (2 * v) ≤ a⁻¹ := (lt_of_not_ge h).le
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (b : ℝ) / (2 * v)) hle r
      have hbound := killFraction_le_pow hbv (Nat.le_of_lt hrv) hv
      exact hx (hbound.trans hpow)
    have hat : 1 ≤ a * ((b : ℝ) / (2 * v)) := by
      simpa [ne_of_gt ha] using mul_le_mul_of_nonneg_left ht ha.le
    have hqlo := killFraction_succ_lower hrb hrv
    have hprod : (2 * (r + 1 : ℝ) * a) *
        (x * ((b : ℝ) / (2 * v)) / (r + 1)) ≤ (g : ℝ) * q :=
      mul_le_mul hg hqlo (by positivity) (by positivity)
    have hrpos : (r + 1 : ℝ) ≠ 0 := by positivity
    have heq : (2 * (r + 1 : ℝ) * a) *
        (x * ((b : ℝ) / (2 * v)) / (r + 1)) =
        2 * x * (a * ((b : ℝ) / (2 * v))) := by
      field_simp
    rw [heq] at hprod
    have hdbl : 2 * x ≤ (g : ℝ) * q := by
      nlinarith [mul_le_mul_of_nonneg_left hat (by positivity : 0 ≤ 2 * x)]
    have hb := block_ge_of_double hx0 hxhalf hq0 hq1 hdbl
    have heps : 0 ≤ a⁻¹ ^ r := by positivity
    change x - a⁻¹ ^ r ≤ 1 - (1 - q) ^ g
    linarith

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
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_FiniteMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_congr {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a = g a) : uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl (fun a _ => h a)

theorem uniformMean_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformMean (fun _ : α => c) = c := by
  simp [uniformMean, ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos :
    (0 : ℝ) < Fintype.card α)]

theorem uniformMean_zero {α : Type*} [Fintype α] :
    uniformMean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [uniformMean]

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp only [uniformMean, ← Finset.sum_mul]
  ring

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    uniformMean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem uniformMean_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem uniformMean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformMean (fun a => f (e a)) = uniformMean f := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α × β → ℝ) : uniformMean f = uniformMean (fun a => uniformMean (fun b => f (a,b))) := by
  simp only [uniformMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div]
  ring

theorem uniformMean_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean (fun a => f a b)) := by
  simp only [uniformMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

theorem uniformMean_sq_sub {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => (f a - c)^2) =
      uniformMean (fun a => f a ^ 2) - 2 * c * uniformMean f + c^2 := by
  calc
    _ = uniformMean (fun a => (f a ^ 2 - (2 * c) * f a) + c^2) :=
      uniformMean_congr (fun _ => by ring)
    _ = _ := by rw [uniformMean_add, uniformMean_sub, uniformMean_const_mul, uniformMean_const]

theorem uniformMean_sq_ge {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : uniformMean f ^ 2 ≤ uniformMean (fun a => f a ^ 2) := by
  have h := uniformMean_nonneg (fun a => sq_nonneg (f a - uniformMean f))
  rw [uniformMean_sq_sub] at h
  nlinarith

theorem uniformVariance_eq {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : uniformVariance f = uniformMean (fun a => f a^2) - uniformMean f ^ 2 := by
  rw [uniformVariance, uniformMean_sq_sub]
  ring

theorem uniformVariance_le_sq_dist {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) : uniformVariance f ≤ uniformMean (fun a => (f a - c)^2) := by
  rw [uniformVariance_eq, uniformMean_sq_sub]
  nlinarith [sq_nonneg (uniformMean f - c)]

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_ClauseProcess
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem addClause_comm {n k r : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (D : ProperClause n r) :
    addClause (addClause S C) D = addClause (addClause S D) C := by
  ext σ
  simp only [mem_addClause]
  tauto

theorem restrictSolutions_zero {n k : ℕ} (S : Finset (Assignment n))
    (F : Formula n k 0) : restrictSolutions S F = S := by
  ext σ
  simp only [mem_restrictSolutions, Fin.forall_fin_zero, and_true]

theorem restrictSolutions_cons {n k m : ℕ} (S : Finset (Assignment n))
    (C : ProperClause n k) (F : Formula n k m) :
    restrictSolutions S (Fin.cons C F) = restrictSolutions (addClause S C) F := by
  ext σ
  simp only [mem_restrictSolutions, mem_addClause, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ]
  tauto

theorem uniformMean_fin_succ {α : Type*} [Fintype α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformMean f = uniformMean (fun a => uniformMean (fun F : Fin m → α =>
      f (Fin.cons a F))) := by
  calc
    _ = uniformMean (fun p : α × (Fin m → α) => f (Fin.cons p.1 p.2)) :=
      (uniformMean_equiv (Fin.consEquiv (fun _ => α)) f).symm
    _ = _ := uniformMean_prod _

theorem alive_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ alive S := by
  unfold alive
  split <;> norm_num

theorem alive_le_one {n : ℕ} (S : Finset (Assignment n)) : alive S ≤ 1 := by
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

theorem survival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k (m + 1) S = uniformMean (fun C : ProperClause n k =>
      survival k m (addClause S C)) := by
  rw [survival, Function.iterate_succ_apply']
  rfl

theorem survival_eq_mean {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformMean (fun F : Formula n k m => alive (restrictSolutions S F)) := by
  induction m generalizing S with
  | zero =>
    simp only [survival_zero, restrictSolutions_zero]
    exact (uniformMean_const _).symm
  | succ m ih =>
    rw [survival_succ, uniformMean_fin_succ]
    apply uniformMean_congr
    intro C
    rw [ih]
    apply uniformMean_congr
    intro F
    rw [restrictSolutions_cons]

theorem properSATProbability_eq_survival (n k m : ℕ) :
    properSATProbability n k m = survival k m (Finset.univ : Finset (Assignment n)) := by
  rw [survival_eq_mean]
  change uniformProbability (fun F : Formula n k m => Satisfiable F) = _
  rw [uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  simp only [Finset.nonempty_iff_ne_empty]
  apply propext
  rw [← Finset.nonempty_iff_ne_empty]
  simp [Finset.Nonempty, Satisfiable, Satisfies]

theorem survival_nonneg {n k m : ℕ} (S : Finset (Assignment n)) : 0 ≤ survival k m S := by
  rw [survival_eq_mean]
  exact uniformMean_nonneg (fun _ => alive_nonneg _)

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

theorem clauseAverage_mono {n k : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, clauseAverage k f S ≤ clauseAverage k g S := by
  intro S
  exact uniformMean_mono (fun C => hfg (addClause S C))

theorem clauseAverage_sub_const {n k : ℕ} (hkn : k ≤ n)
    (f : Finset (Assignment n) → ℝ) (c : ℝ) (S : Finset (Assignment n)) :
    clauseAverage k (fun T => f T - c) S = clauseAverage k f S - c := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  exact (uniformMean_sub _ _).trans (by rw [uniformMean_const]; rfl)

theorem clauseAverage_commute {n k r : ℕ} :
    Function.Commute (clauseAverage (n := n) k) (clauseAverage r) := by
  intro f
  funext S
  unfold clauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro C
  apply uniformMean_congr
  intro D
  rw [addClause_comm]

theorem clauseAverage_iterate_mono {n k m : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S,
    ((clauseAverage k)^[m] f) S ≤ ((clauseAverage k)^[m] g) S := by
  induction m with
  | zero => exact hfg
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    exact clauseAverage_mono ih

theorem clauseAverage_iterate_sub_const {n k m : ℕ} (hkn : k ≤ n)
    (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    (clauseAverage k)^[m] (fun T => f T - c) =
      (fun S => ((clauseAverage k)^[m] f) S - c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    funext S
    exact clauseAverage_sub_const hkn _ _ _

theorem survival_shift {n k r m d : ℕ} (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] (survival r d)) S =
      ((clauseAverage r)^[d] (survival k m)) S := by
  exact congrArg (fun f => f S) ((clauseAverage_commute (n := n) (k := k) (r := r)).iterate_iterate m d alive)

theorem survival_add {n k m d : ℕ} (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] (survival k d)) S = survival k (m + d) S := by
  exact congrArg (fun f => f S) (Function.iterate_add_apply (clauseAverage k) m d alive).symm

theorem survival_eq_probability {n k m : ℕ} (S : Finset (Assignment n)) :
    survival k m S = uniformProbability (fun F : Formula n k m =>
      ∃ σ ∈ S, Satisfies σ F) := by
  rw [survival_eq_mean, uniformProbability_eq_mean]
  apply uniformMean_congr
  intro F
  unfold alive
  congr 1
  apply propext
  simp [Finset.Nonempty, Satisfies]

theorem blockUNSAT_eq {n k g : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    blockUNSATProbability k g S = 1 - survival k g S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [survival_eq_probability]
  exact uniformProbability_not _

theorem kills_iff_addClause {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    KillsSolutions S C ↔ ¬ (addClause S C).Nonempty := by
  change (∀ σ ∈ S, ¬ SatisfiesClause σ C) ↔ ¬ ∃ σ, σ ∈ addClause S C
  simp only [mem_addClause, not_exists, not_and]

theorem singleUNSAT_eq {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    uniformProbability (fun C : ProperClause n k => KillsSolutions S C) =
      1 - survival k 1 S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [uniformProbability_eq_mean, survival_succ]
  simp only [survival_zero]
  calc
    _ = uniformMean (fun C : ProperClause n k => 1 - alive (addClause S C)) := by
      apply uniformMean_congr
      intro C
      rw [kills_iff_addClause]
      unfold alive
      by_cases h : (addClause S C).Nonempty <;> simp [h]
    _ = _ := by rw [uniformMean_sub, uniformMean_const]

theorem shorter_survival_replacement {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    survival k (replacementBlock n k) S - replacementError n k ≤ survival (k - 1) 1 S := by
  have h := shorter_clause_replacement hk hn S
  rw [singleUNSAT_eq (by omega), blockUNSAT_eq (by omega)] at h
  linarith

theorem uniformMean_sum_type {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (f : α ⊕ β → ℝ) :
    uniformMean f =
      ((Fintype.card α : ℝ) / (Fintype.card α + Fintype.card β)) *
        uniformMean (fun a => f (Sum.inl a)) +
      ((Fintype.card β : ℝ) / (Fintype.card α + Fintype.card β)) *
        uniformMean (fun b => f (Sum.inr b)) := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [uniformMean, Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add]
  field_simp

theorem head_incidence_ratio {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v) :
    ((v.choose (k - 1) * 2 ^ (k - 1) * 2 : ℕ) : ℝ) /
      ((v.choose k * 2 ^ k + v.choose (k - 1) * 2 ^ (k - 1) * 2 : ℕ) : ℝ) =
      (k : ℝ) / (v + 1) := by
  have hks : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hch : v.choose k + v.choose (k - 1) = (v + 1).choose k := by
    simpa only [Nat.succ_eq_add_one, hks, add_comm] using (Nat.choose_succ_succ v (k - 1)).symm
  have hmult : ((v : ℝ) + 1) * (v.choose (k - 1) : ℝ) =
      ((v + 1).choose k : ℝ) * (k : ℝ) := by
    exact_mod_cast (by simpa only [hks] using Nat.add_one_mul_choose_eq v (k - 1))
  have hpow : (2 : ℝ) ^ (k - 1) * 2 = 2 ^ k := by
    rw [← pow_succ, hks]
  have hcpos : (0 : ℝ) < (v + 1).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ v + 1)
  have hvpos : (0 : ℝ) < (v : ℝ) + 1 := by positivity
  push_cast
  simp only [mul_assoc, hpow]
  rw [← add_mul]
  have hc : (v.choose k : ℝ) + v.choose (k - 1) = (v + 1).choose k := by
    exact_mod_cast hch
  rw [hc]
  apply (div_eq_div_iff (by positivity) hvpos.ne').mpr
  nlinarith [congrArg (fun z : ℝ => z * 2 ^ k) hmult]

theorem clauseHead_mean {v k : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (f : (ProperClause v k ⊕ (ProperClause v (k - 1) × Bool)) → ℝ) :
    uniformMean (fun C : ProperClause (v + 1) k => f (clauseHeadSplit hk C)) =
      (1 - (k : ℝ) / (v + 1)) * uniformMean (fun C => f (Sum.inl C)) +
      ((k : ℝ) / (v + 1)) *
        uniformMean (fun Q => uniformMean (fun b : Bool => f (Sum.inr (Q, b)))) := by
  let : Nonempty (ProperClause v k) := nonempty_properClause hkv
  let : Nonempty (ProperClause v (k - 1)) := nonempty_properClause (by omega)
  change uniformMean (fun C => f (clauseHeadEquiv hk C)) = _
  rw [uniformMean_equiv, uniformMean_sum_type, uniformMean_prod]
  have hr := head_incidence_ratio hk hkv
  have ht : (0 : ℝ) < Fintype.card (ProperClause v k) +
      Fintype.card (ProperClause v (k - 1) × Bool) := by
    exact add_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hr' : (Fintype.card (ProperClause v (k - 1) × Bool) : ℝ) /
      (Fintype.card (ProperClause v k) + Fintype.card (ProperClause v (k - 1) × Bool)) =
      (k : ℝ) / (v + 1) := by
    simpa only [Fintype.card_prod, Fintype.card_bool, card_properClause, Nat.cast_add] using hr
  rw [hr', ← hr']
  congr 1
  apply congrArg (fun x : ℝ => x * uniformMean (fun C => f (Sum.inl C)))
  field_simp
  ring

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Binomial
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem binomialMean_sum {ι : Type*} (p : ℝ) (m : ℕ) (s : Finset ι) (f : ι → ℕ → ℝ) :
    binomialMean p m (fun d => ∑ i ∈ s, f i d) = ∑ i ∈ s, binomialMean p m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [binomialMean_const]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, binomialMean_add, ih]

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

theorem binomialMean_monotone_trials {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : Monotone f) : Monotone (fun m => binomialMean p m f) := by
  apply monotone_nat_of_le_succ
  intro m
  have h := binomialMean_mono (m := m) hp0 hp1 (f := f) (g := fun d => f (d + 1))
    (fun d _ => hf (by omega))
  change _ ≤ (1 - p) * _ + p * _
  nlinarith

theorem uniformMean_binomialMean {α : Type*} [Fintype α]
    (p : ℝ) (m : ℕ) (f : ℕ → α → ℝ) :
    uniformMean (fun a => binomialMean p m (fun d => f d a)) =
      binomialMean p m (fun d => uniformMean (f d)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [binomialMean, uniformMean_add, uniformMean_const_mul, ih]

theorem sum_shift_difference_le (P : ℕ → ℝ) (hP0 : ∀ j, 0 ≤ P j)
    (hP1 : ∀ j, P j ≤ 1) (l b : ℕ) :
    ∑ j ∈ Finset.range l, (P j - P (j + b)) ≤ (b : ℝ) := by
  have h1 := Finset.sum_range_add P l b
  have h2 := Finset.sum_range_add P b l
  have hid : (∑ j ∈ Finset.range l, (P j - P (j + b))) =
      ∑ j ∈ Finset.range b, (P j - P (j + l)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have hc : l + b = b + l := Nat.add_comm _ _
    simp only [Nat.add_comm l] at h1
    simp only [Nat.add_comm b] at h2
    rw [hc] at h2
    linarith
  rw [hid]
  calc
    _ ≤ ∑ _j ∈ Finset.range b, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      linarith [hP0 (j + l), hP1 j]
    _ = b := by simp

theorem sum_two_shift_difference_le (P : ℕ → ℝ) (hP0 : ∀ j, 0 ≤ P j)
    (hP1 : ∀ j, P j ≤ 1) (l a b : ℕ) :
    ∑ j ∈ Finset.range l, (P (j - a) - P (j + b)) ≤ (a : ℝ) + b := by
  have h1 := sum_shift_difference_le (fun j => P (j - a))
    (fun j => hP0 _) (fun j => hP1 _) l a
  simp only [Nat.add_sub_cancel] at h1
  have h2 := sum_shift_difference_le P hP0 hP1 l b
  have he : (∑ j ∈ Finset.range l, (P (j - a) - P (j + b))) =
      (∑ j ∈ Finset.range l, (P (j - a) - P j)) +
      ∑ j ∈ Finset.range l, (P j - P (j + b)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

theorem replacementDifference_mono {P : ℕ → ℝ} (hP : Antitone P) (g j : ℕ) :
    Monotone (replacementDifference P g j) := by
  intro d e hde
  apply sub_le_sub
  · exact hP (Nat.sub_le_sub_left hde j)
  · exact hP (Nat.add_le_add_left (Nat.mul_le_mul_left _ hde) j)

theorem replacementDifference_sum_le {P : ℕ → ℝ}
    (hP0 : ∀ j, 0 ≤ P j) (hP1 : ∀ j, P j ≤ 1) {g : ℕ} (hg : 1 ≤ g) (l d : ℕ) :
    ∑ j ∈ Finset.range l, replacementDifference P g j d ≤ (g : ℝ) * d := by
  have h := sum_two_shift_difference_le P hP0 hP1 l d ((g - 1) * d)
  have he : (d : ℝ) + ((g - 1) * d : ℕ) = (g : ℝ) * d := by
    rw [Nat.cast_mul, Nat.cast_sub hg]
    push_cast
    ring
  simpa only [replacementDifference, he] using h

theorem binomial_replacement_sum_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P : ℕ → ℝ} (hP : Antitone P) (hP0 : ∀ j, 0 ≤ P j) (hP1 : ∀ j, P j ≤ 1)
    {g : ℕ} (hg : 1 ≤ g) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), binomialMean p j (replacementDifference P g j) ≤
      (g : ℝ) * (M : ℝ) * p := by
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1), binomialMean p M (replacementDifference P g j) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjM : j ≤ M := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
      exact binomialMean_monotone_trials hp0 hp1 (replacementDifference_mono hP g j) hjM
    _ = binomialMean p M (fun d => ∑ j ∈ Finset.range (M + 1),
        replacementDifference P g j d) := (binomialMean_sum _ _ _ _).symm
    _ ≤ binomialMean p M (fun d => (g : ℝ) * d) :=
      binomialMean_mono hp0 hp1 (fun d _ => replacementDifference_sum_le hP0 hP1 hg _ d)
    _ = _ := by rw [binomialMean_const_mul, binomialMean_id]; ring

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Forcing
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Deletion and erasure of a coordinate, permutation symmetry, and the integrated
forcing bound.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem erasedSolutions_subset {v k m : ℕ} (S : Finset (Assignment v))
    (F : Fin m → SplitClause v k) : erasedSolutions S F ⊆ deletedSolutions S F := by
  intro σ hσ
  rw [mem_erasedSolutions] at hσ
  rw [mem_deletedSolutions]
  refine ⟨hσ.1, fun i => ?_⟩
  have hi := hσ.2 i
  cases hFi : F i with
  | inl C => simpa [ErasedSatisfied, DeletedSatisfied, hFi] using hi
  | inr Q => trivial

theorem satisfies_head_split {v k : ℕ} (hk : 0 < k) (σ : Assignment v)
    (b : Bool) (X : SplitClause v k) :
    SatisfiesClause (Fin.cons b σ) ((clauseHeadEquiv hk).symm X) ↔
      match X with
      | .inl C => SatisfiesClause σ C
      | .inr Q => Q.2 = b ∨ SatisfiesClause σ Q.1 := by
  cases X with
  | inl C => exact satisfiesClause_prependAbsent σ b C
  | inr Q => exact satisfiesClause_prependPresent hk σ b Q.2 Q.1

theorem head_erasure_extension {v k m : ℕ} (hk : 0 < k)
    (F : Fin m → SplitClause v k) {σ : Assignment v}
    (hσ : σ ∈ erasedSolutions Finset.univ F) (b : Bool) :
    Satisfies (Fin.cons b σ) (fun i => (clauseHeadEquiv hk).symm (F i)) := by
  intro i
  rw [satisfies_head_split]
  have hi := ((mem_erasedSolutions _ _ _).mp hσ).2 i
  cases hFi : F i with
  | inl C => simpa [ErasedSatisfied, hFi] using hi
  | inr Q => exact Or.inr (by simpa [ErasedSatisfied, hFi] using hi)

theorem head_deletion_projection {v k m : ℕ} (hk : 0 < k)
    (F : Fin m → SplitClause v k) {σ : Assignment (v + 1)}
    (hσ : Satisfies σ (fun i => (clauseHeadEquiv hk).symm (F i))) :
    Fin.tail σ ∈ deletedSolutions Finset.univ F := by
  rw [mem_deletedSolutions]
  refine ⟨Finset.mem_univ _, fun i => ?_⟩
  have hi := hσ i
  rw [← Fin.cons_self_tail σ, satisfies_head_split] at hi
  cases hFi : F i with
  | inl C => simpa [DeletedSatisfied, hFi] using hi
  | inr Q => trivial

theorem head_forced_reduction {v k m : ℕ} (hk : 0 < k) (F : Fin m → SplitClause v k)
    (hf : (0 : Fin (v + 1)) ∈ forcedVariables
      (restrictSolutions Finset.univ (fun i => (clauseHeadEquiv hk).symm (F i)))) :
    (deletedSolutions Finset.univ F).Nonempty ∧ ¬ (erasedSolutions Finset.univ F).Nonempty := by
  simp only [forcedVariables, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  obtain ⟨σ, hσ⟩ := hf.1
  have hsat : Satisfies σ (fun i => (clauseHeadEquiv hk).symm (F i)) :=
    ((mem_restrictSolutions _ _ _).mp hσ).2
  refine ⟨⟨Fin.tail σ, head_deletion_projection hk F hsat⟩, ?_⟩
  rintro ⟨τ, hτ⟩
  obtain ⟨b, hb⟩ := hf.2
  have hext (t : Bool) : Fin.cons t τ ∈
      restrictSolutions Finset.univ (fun i => (clauseHeadEquiv hk).symm (F i)) := by
    rw [mem_restrictSolutions]
    exact ⟨Finset.mem_univ _, head_erasure_extension hk F hτ t⟩
  have hfalse := hb _ (hext false)
  have htrue := hb _ (hext true)
  simp only [Fin.cons_zero] at hfalse htrue
  cases b <;> simp_all

theorem head_forced_indicator_le {v k m : ℕ} (hk : 0 < k) (F : Fin m → SplitClause v k) :
    (if (0 : Fin (v + 1)) ∈ forcedVariables
      (restrictSolutions Finset.univ (fun i => (clauseHeadEquiv hk).symm (F i)))
      then (1 : ℝ) else 0) ≤
      alive (deletedSolutions Finset.univ F) - alive (erasedSolutions Finset.univ F) := by
  split
  · rename_i h
    obtain ⟨hd, he⟩ := head_forced_reduction hk F h
    simp [alive, hd, he]
  · have h := alive_mono (erasedSolutions_subset Finset.univ F)
    linarith

theorem deletedSolutions_cons_inl {v k m : ℕ} (S : Finset (Assignment v))
    (C : ProperClause v k) (F : Fin m → SplitClause v k) :
    deletedSolutions S (Fin.cons (.inl C) F) = deletedSolutions (addClause S C) F := by
  ext σ
  simp only [mem_deletedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, DeletedSatisfied]
  tauto

theorem deletedSolutions_cons_inr {v k m : ℕ} (S : Finset (Assignment v))
    (Q : ProperClause v (k - 1)) (b : Bool) (F : Fin m → SplitClause v k) :
    deletedSolutions S (Fin.cons (.inr (Q, b)) F) = deletedSolutions S F := by
  ext σ
  simp only [mem_deletedSolutions, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, DeletedSatisfied, true_and]

theorem erasedSolutions_cons_inl {v k m : ℕ} (S : Finset (Assignment v))
    (C : ProperClause v k) (F : Fin m → SplitClause v k) :
    erasedSolutions S (Fin.cons (.inl C) F) = erasedSolutions (addClause S C) F := by
  ext σ
  simp only [mem_erasedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, ErasedSatisfied]
  tauto

theorem erasedSolutions_cons_inr {v k m : ℕ} (S : Finset (Assignment v))
    (Q : ProperClause v (k - 1)) (b : Bool) (F : Fin m → SplitClause v k) :
    erasedSolutions S (Fin.cons (.inr (Q, b)) F) = erasedSolutions (addClause S Q) F := by
  ext σ
  simp only [mem_erasedSolutions, mem_addClause, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, ErasedSatisfied]
  tauto

@[simp] theorem deletedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    deletedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      deletedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [deletedMean, h, uniformMean_const]

@[simp] theorem erasedMean_zero {v k : ℕ} (hk : 0 < k) (S : Finset (Assignment v)) :
    erasedMean hk 0 S = alive S := by
  have h (F : Formula (v + 1) k 0) :
      erasedSolutions S (fun i => clauseHeadSplit hk (F i)) = S := by
    ext σ
    simp
  simp only [erasedMean, h, uniformMean_const]

theorem deletedMean_succ {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    deletedMean hk (m + 1) S =
      (1 - (k : ℝ) / (v + 1)) * clauseAverage k (deletedMean hk m) S +
      ((k : ℝ) / (v + 1)) * deletedMean hk m S := by
  let : Nonempty (ProperClause v (k - 1)) := nonempty_properClause (by omega)
  unfold deletedMean
  rw [uniformMean_fin_succ]
  have hcons (C : ProperClause (v + 1) k) (F : Formula (v + 1) k m) :
      (fun i : Fin (m + 1) => clauseHeadSplit hk ((Fin.cons C F : Formula (v + 1) k (m + 1)) i)) =
        Fin.cons (clauseHeadSplit hk C) (fun i => clauseHeadSplit hk (F i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [hcons]
  rw [clauseHead_mean hk hkv (fun X => uniformMean (fun F : Formula (v + 1) k m =>
    alive (deletedSolutions S (Fin.cons X (fun i => clauseHeadSplit hk (F i))))))]
  simp only [deletedSolutions_cons_inl, deletedSolutions_cons_inr,
    uniformMean_const]
  rfl

theorem erasedMean_succ {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    erasedMean hk (m + 1) S =
      (1 - (k : ℝ) / (v + 1)) * clauseAverage k (erasedMean hk m) S +
      ((k : ℝ) / (v + 1)) * clauseAverage (k - 1) (erasedMean hk m) S := by
  unfold erasedMean
  rw [uniformMean_fin_succ]
  have hcons (C : ProperClause (v + 1) k) (F : Formula (v + 1) k m) :
      (fun i : Fin (m + 1) => clauseHeadSplit hk ((Fin.cons C F : Formula (v + 1) k (m + 1)) i)) =
        Fin.cons (clauseHeadSplit hk C) (fun i => clauseHeadSplit hk (F i)) := by
    funext i
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  simp only [hcons]
  rw [clauseHead_mean hk hkv (fun X => uniformMean (fun F : Formula (v + 1) k m =>
    alive (erasedSolutions S (Fin.cons X (fun i => clauseHeadSplit hk (F i))))))]
  simp only [erasedSolutions_cons_inl, erasedSolutions_cons_inr,
    uniformMean_const]
  rfl

theorem clauseAverage_binomialMean {v k : ℕ} (p : ℝ) (m : ℕ)
    (f : ℕ → Finset (Assignment v) → ℝ) (S : Finset (Assignment v)) :
    clauseAverage k (fun T => binomialMean p m (fun d => f d T)) S =
      binomialMean p m (fun d => clauseAverage k (f d) S) :=
  uniformMean_binomialMean p m _

theorem clauseAverage_survival {v k t : ℕ} (S : Finset (Assignment v)) :
    clauseAverage k (survival k t) S = survival k (t + 1) S :=
  (survival_succ S).symm

theorem clauseAverage_short_survival {n k t : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    survival k (t + replacementBlock n k) S - replacementError n k ≤
      clauseAverage (k - 1) (survival k t) S := by
  have h := clauseAverage_iterate_mono (k := k) (m := t)
    (shorter_survival_replacement hk hn) S
  rw [clauseAverage_iterate_sub_const (by omega)] at h
  dsimp only at h
  rw [survival_add] at h
  have he : clauseAverage (k - 1) (survival k t) S =
      ((clauseAverage k)^[t] (survival (k - 1) 1)) S :=
    survival_shift (m := 1) (d := t) S
  rw [he]
  simpa using h

theorem deletedMean_eq_binomial {v k m : ℕ} (hk : 0 < k) (hkv : k ≤ v)
    (S : Finset (Assignment v)) :
    deletedMean hk m S = binomialMean ((k : ℝ) / (v + 1)) m
      (fun d => survival k (m - d) S) := by
  induction m generalizing S with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [deletedMean_succ hk hkv]
    have hfun : deletedMean hk m =
        (fun T : Finset (Assignment v) => binomialMean ((k : ℝ) / (v + 1)) m
          (fun d => survival k (m - d) T)) := funext ih
    rw [hfun, clauseAverage_binomialMean]
    change _ = (1 - (k : ℝ) / (v + 1)) * _ + ((k : ℝ) / (v + 1)) * _
    congr 1
    · congr 1
      apply binomialMean_congr
      intro d hd
      rw [clauseAverage_survival]
      congr 1
      omega
    · congr 1
      apply binomialMean_congr
      intro d _
      congr 1
      omega

theorem erasedMean_replacement {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    (S : Finset (Assignment (n - 1))) :
    binomialMean ((k : ℝ) / n) m (fun d =>
      survival k (m - d + replacementBlock n k * d) S -
        (d : ℝ) * replacementError n k) ≤ erasedMean (by omega : 0 < k) m S := by
  have hkn : k ≤ n - 1 := by omega
  have hshort : k - 1 ≤ n - 1 := by omega
  have hn1 : n - 1 + 1 = n := by omega
  have hp0 : 0 ≤ (k : ℝ) / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (by omega : 0 < n))).mpr
    exact_mod_cast (by omega : k ≤ n)
  induction m generalizing S with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [erasedMean_succ (by omega) hkn]
    have hden : ((n - 1 : ℕ) : ℝ) + 1 = n := by exact_mod_cast hn1
    rw [hden]
    have hlong := clauseAverage_mono (k := k) ih S
    have hshorter := clauseAverage_mono (k := k - 1) ih S
    rw [clauseAverage_binomialMean] at hlong hshorter
    have ha : binomialMean ((k : ℝ) / n) m (fun d =>
        survival k (m + 1 - d + replacementBlock n k * d) S -
          (d : ℝ) * replacementError n k) ≤ clauseAverage k (erasedMean (by omega : 0 < k) m) S := by
      calc
        _ = binomialMean ((k : ℝ) / n) m (fun d => clauseAverage k
            (fun T => survival k (m - d + replacementBlock n k * d) T -
              (d : ℝ) * replacementError n k) S) := by
          apply binomialMean_congr
          intro d hd
          rw [clauseAverage_sub_const hkn, clauseAverage_survival]
          congr 2
          omega
        _ ≤ _ := hlong
    have hb : binomialMean ((k : ℝ) / n) m (fun d =>
        survival k (m + 1 - (d + 1) + replacementBlock n k * (d + 1)) S -
          ((d + 1 : ℕ) : ℝ) * replacementError n k) ≤
        clauseAverage (k - 1) (erasedMean (by omega : 0 < k) m) S := by
      apply le_trans _ hshorter
      apply binomialMean_mono hp0 hp1
      intro d _
      rw [clauseAverage_sub_const hshort]
      have h := clauseAverage_short_survival (t := m - d + replacementBlock n k * d) hk hn S
      have he : m + 1 - (d + 1) + replacementBlock n k * (d + 1) =
          m - d + replacementBlock n k * d + replacementBlock n k := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      rw [he]
      push_cast
      linarith
    exact add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hp1))
      (mul_le_mul_of_nonneg_left hb hp0)

theorem replacementBlock_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    1 ≤ replacementBlock n k := by
  have hp : 0 < 2 * (k : ℝ) * replacementScale n k :=
    mul_pos (mul_pos (by norm_num) (by exact_mod_cast hk)) (replacementScale_pos hn)
  exact Nat.ceil_pos.mpr hp

theorem replacementError_nonneg (n k : ℕ) : 0 ≤ replacementError n k := by
  unfold replacementError replacementScale
  positivity

theorem headForcedMean_le_difference {v k m : ℕ} (hk : 0 < k) :
    headForcedMean v k m ≤ deletedMean (v := v) hk m Finset.univ - erasedMean (v := v) hk m Finset.univ := by
  unfold headForcedMean deletedMean erasedMean
  rw [← uniformMean_sub]
  apply uniformMean_mono
  intro F
  have he : (fun i => (clauseHeadEquiv hk).symm (clauseHeadSplit hk (F i))) = F := by
    funext i
    exact (clauseHeadEquiv hk).symm_apply_apply (F i)
  have h := head_forced_indicator_le hk (fun i => clauseHeadSplit hk (F i))
  simpa only [he] using h

theorem headForcedMean_replacement {v k m : ℕ} (hk : 3 ≤ k) (hkv : k ≤ v) :
    headForcedMean v k m ≤
      binomialMean ((k : ℝ) / (v + 1)) m
        (replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) m) +
      ((m : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k := by
  have hdel := deletedMean_eq_binomial (m := m) (by omega : 0 < k) hkv Finset.univ
  have her := erasedMean_replacement (n := v + 1) (m := m) hk (by omega) Finset.univ
  simp only [Nat.cast_add, Nat.cast_one] at her
  have hforced := headForcedMean_le_difference (v := v) (m := m) (by omega : 0 < k)
  rw [hdel] at hforced
  have hsub : (binomialMean ((k : ℝ) / (v + 1)) m (fun d => survival k (m - d)
      (Finset.univ : Finset (Assignment v)))) -
      binomialMean ((k : ℝ) / (v + 1)) m (fun d =>
        survival k (m - d + replacementBlock (v + 1) k * d)
          (Finset.univ : Finset (Assignment v)) -
          (d : ℝ) * replacementError (v + 1) k) =
      binomialMean ((k : ℝ) / (v + 1)) m
        (replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) m) +
      ((m : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k := by
    rw [← binomialMean_sub]
    have hg : 1 ≤ replacementBlock (v + 1) k := replacementBlock_pos (by omega) (by omega)
    calc
      _ = binomialMean ((k : ℝ) / (v + 1)) m (fun d =>
          replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) m d +
            (d : ℝ) * replacementError (v + 1) k) := by
        apply binomialMean_congr
        intro d hd
        unfold replacementDifference
        rw [properSATProbability_eq_survival, properSATProbability_eq_survival]
        have he : m - d + replacementBlock (v + 1) k * d =
            m + (replacementBlock (v + 1) k - 1) * d := by
          have hh := Nat.sub_add_cancel hg
          have := congrArg (fun a : ℕ => a * d) hh
          simp only [Nat.add_mul, Nat.one_mul] at this
          omega
        rw [he]
        ring
      _ = _ := by rw [binomialMean_add, binomialMean_mul_const, binomialMean_id]
  rw [← hsub]
  linarith

theorem integrated_head_forcing {v k : ℕ} (hk : 3 ≤ k) (hkv : k ≤ v) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), headForcedMean v k j ≤
      (replacementBlock (v + 1) k : ℝ) * M * ((k : ℝ) / (v + 1)) +
      ((M + 1 : ℕ) : ℝ) * M * ((k : ℝ) / (v + 1)) * replacementError (v + 1) k := by
  have hp0 : 0 ≤ (k : ℝ) / (v + 1) := by positivity
  have hp1 : (k : ℝ) / (v + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast (by omega : k ≤ v + 1)
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1),
        (binomialMean ((k : ℝ) / (v + 1)) j
          (replacementDifference (properSATProbability v k) (replacementBlock (v + 1) k) j) +
        ((j : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k) :=
      Finset.sum_le_sum (fun _ _ => headForcedMean_replacement hk hkv)
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by
      apply add_le_add
      · exact binomial_replacement_sum_le hp0 hp1 (properSATProbability_antitone hkv)
          (fun j => properSATProbability_nonneg v k j) (fun j => properSATProbability_le_one v k j)
          (replacementBlock_pos (by omega) (by omega)) M
      · calc
          _ ≤ ∑ _j ∈ Finset.range (M + 1),
              ((M : ℝ) * ((k : ℝ) / (v + 1))) * replacementError (v + 1) k := by
            apply Finset.sum_le_sum
            intro j hj
            have hjM : (j : ℝ) ≤ M := by
              exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjM hp0)
              (replacementError_nonneg (v + 1) k)
          _ = _ := by simp; ring

theorem satisfiesClause_rename {n k : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n)
    (C : ProperClause n k) :
    SatisfiesClause (renameAssignment e σ) (renameClause e C) ↔ SatisfiesClause σ C := by
  change (∃ i, C.val (e i) = some (σ (e i))) ↔ ∃ i, C.val i = some (σ i)
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa using hi⟩

theorem satisfies_rename {n k m : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n)
    (F : Formula n k m) :
    Satisfies (renameAssignment e σ) (renameFormula e F) ↔ Satisfies σ F := by
  simp only [Satisfies, renameFormula, satisfiesClause_rename]

theorem satisfies_rename_inverse {n k m : ℕ} (e : Fin n ≃ Fin n) (σ : Assignment n)
    (F : Formula n k m) :
    Satisfies σ (renameFormula e F) ↔ Satisfies (renameAssignment e.symm σ) F := by
  have h := satisfies_rename e (renameAssignment e.symm σ) F
  have he : renameAssignment e (renameAssignment e.symm σ) = σ := by
    funext i
    exact congrArg σ (e.symm_apply_apply i)
  rw [he] at h
  exact h

theorem satisfiable_rename {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) :
    Satisfiable (renameFormula e F) ↔ Satisfiable F := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨renameAssignment e.symm σ, (satisfies_rename_inverse e σ F).mp hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨renameAssignment e σ, (satisfies_rename e σ F).mpr hσ⟩

theorem mem_forced_formula {n k m : ℕ} (F : Formula n k m) (i : Fin n) :
    i ∈ forcedVariables (restrictSolutions Finset.univ F) ↔
      Satisfiable F ∧ ∃ b, ∀ σ, Satisfies σ F → σ i = b := by
  simp [forcedVariables, Finset.Nonempty, Satisfiable, Satisfies]

theorem forcedVariables_rename {n k m : ℕ} (e : Fin n ≃ Fin n) (F : Formula n k m) (i : Fin n) :
    i ∈ forcedVariables (restrictSolutions Finset.univ (renameFormula e F)) ↔
      e i ∈ forcedVariables (restrictSolutions Finset.univ F) := by
  rw [mem_forced_formula, mem_forced_formula, satisfiable_rename]
  constructor
  · rintro ⟨hS, b, hb⟩
    refine ⟨hS, b, fun σ hσ => ?_⟩
    exact hb (renameAssignment e σ) ((satisfies_rename e σ F).mpr hσ)
  · rintro ⟨hS, b, hb⟩
    refine ⟨hS, b, fun σ hσ => ?_⟩
    have h := hb (renameAssignment e.symm σ) ((satisfies_rename_inverse e σ F).mp hσ)
    simpa only [renameAssignment, Equiv.symm_apply_apply] using h

theorem forced_coordinate_mean {v k m : ℕ} (i : Fin (v + 1)) :
    uniformMean (fun F : Formula (v + 1) k m =>
      if i ∈ forcedVariables (restrictSolutions Finset.univ F) then (1 : ℝ) else 0) =
        headForcedMean v k m := by
  let e : Fin (v + 1) ≃ Fin (v + 1) := Equiv.swap 0 i
  calc
    _ = uniformMean (fun F : Formula (v + 1) k m =>
        if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ (renameFormula e F)) then (1 : ℝ) else 0) := by
      apply uniformMean_congr
      intro F
      simp only [forcedVariables_rename, e, Equiv.swap_apply_left]
    _ = _ := by
      have h := uniformMean_equiv (renameFormulaEquiv (n := v + 1) (k := k) (m := m) e)
        (fun F : Formula (v + 1) k m => if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ F) then (1 : ℝ) else 0)
      have heq : (fun F : Formula (v + 1) k m => if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ (renameFormula e F)) then (1 : ℝ) else 0) =
          (fun F : Formula (v + 1) k m => if (0 : Fin (v + 1)) ∈ forcedVariables
          (restrictSolutions Finset.univ (renameFormulaEquiv e F)) then (1 : ℝ) else 0) := by
        funext F
        apply ite_congr
        · rfl
        · intro _; rfl
        · intro _; rfl
      rw [heq]
      exact h

theorem forcedFractionMean_eq_head (v k m : ℕ) :
    forcedFractionMean (v + 1) k m = headForcedMean v k m := by
  have hc (F : Formula (v + 1) k m) :
      ((forcedVariables (restrictSolutions Finset.univ F)).card : ℝ) =
        ∑ i : Fin (v + 1), if i ∈ forcedVariables (restrictSolutions Finset.univ F)
          then (1 : ℝ) else 0 := by simp
  unfold forcedFractionMean
  simp_rw [hc, div_eq_mul_inv]
  rw [uniformMean_mul_const, uniformMean_sum]
  simp only [forced_coordinate_mean, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hv : ((v + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem integrated_forcing_finite {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), forcedFractionMean n k j ≤
      (replacementBlock n k : ℝ) * M * ((k : ℝ) / n) +
      ((M + 1 : ℕ) : ℝ) * M * ((k : ℝ) / n) * replacementError n k := by
  cases n with
  | zero => omega
  | succ v =>
    simp only [forcedFractionMean_eq_head]
    simpa only [Nat.cast_add, Nat.cast_one] using integrated_head_forcing hk (by omega) M

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Variance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem addClause_mono {n k : ℕ} {S T : Finset (Assignment n)} (hST : S ⊆ T)
    (C : ProperClause n k) : addClause S C ⊆ addClause T C := by
  intro σ hσ
  rw [mem_addClause] at hσ ⊢
  exact ⟨hST hσ.1, hσ.2⟩

@[simp] theorem survival_empty {n k m : ℕ} : survival k m (∅ : Finset (Assignment n)) = 0 := by
  rw [survival_eq_mean]
  have h (F : Formula n k m) : restrictSolutions ∅ F = ∅ := by simp [restrictSolutions]
  simp only [h, alive_empty, uniformMean_zero]

theorem lifetime_nonneg {n k m : ℕ} (S : Finset (Assignment n)) (F : Formula n k m) :
    0 ≤ lifetime k m S F := by
  induction m generalizing S with
  | zero => exact le_rfl
  | succ m ih => exact add_nonneg (alive_nonneg _) (ih _ _)

theorem lifetimeMean_succ {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    lifetimeMean k (m + 1) S = clauseAverage k (fun T => alive T + lifetimeMean k m T) S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  unfold lifetimeMean
  rw [uniformMean_fin_succ]
  simp only [lifetime_cons, uniformMean_add, uniformMean_const]
  simp only [clauseAverage, uniformMean_add]

theorem clauseAverage_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Finset (Assignment n) → ℝ) (S : Finset (Assignment n)) :
    clauseAverage k (fun T => ∑ i ∈ s, f i T) S =
      ∑ i ∈ s, clauseAverage k (f i) S := uniformMean_sum s _

theorem lifetimeMean_eq_sum {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    lifetimeMean k m S = ∑ j ∈ Finset.range m, survival k (j + 1) S := by
  induction m generalizing S with
  | zero => exact uniformMean_zero
  | succ m ih =>
    rw [lifetimeMean_succ hkn]
    have hfun : (fun T : Finset (Assignment n) => alive T + lifetimeMean k m T) =
        fun T => ∑ j ∈ Finset.range (m + 1), survival k j T := by
      funext T
      rw [Finset.sum_range_succ', ih, survival_zero]
      ring
    rw [hfun, clauseAverage_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact clauseAverage_survival S

theorem killingChance_nonneg {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    0 ≤ killingChance k S := by
  have h := survival_antitone hkn S (Nat.zero_le 1)
  exact sub_nonneg.mpr h

theorem killingChance_le_one {n k : ℕ} (S : Finset (Assignment n)) : killingChance k S ≤ 1 := by
  unfold killingChance
  linarith [alive_le_one S, survival_nonneg (k := k) (m := 1) S]

theorem killingChance_eq_mean {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    killingChance k S = uniformMean (fun C : ProperClause n k => alive S - alive (addClause S C)) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  rw [uniformMean_sub, uniformMean_const]
  rfl

theorem killingChance_eq_probability {n k : ℕ} (hkn : k ≤ n) {S : Finset (Assignment n)}
    (hS : S.Nonempty) :
    killingChance k S = uniformProbability (fun C : ProperClause n k => KillsSolutions S C) := by
  rw [singleUNSAT_eq hkn]
  simp [killingChance, alive, hS]

theorem survival_le_geometric {n k d : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    survival k d S ≤ (1 - killingChance k S) ^ d := by
  by_cases hS : S.Nonempty
  · have h := blockUNSAT_lower (g := d) hkn S
    rw [blockUNSAT_eq hkn, ← killingChance_eq_probability hkn hS] at h
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rw [survival_empty]
    exact pow_nonneg (sub_nonneg.mpr (killingChance_le_one ∅)) _

theorem insertionDelay_zero {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k)
    (F : Formula n k 0) : insertionDelay k 0 S C F = alive S - alive (addClause S C) := by
  simp [insertionDelay]

theorem insertionDelay_cons {n k m : ℕ} (S : Finset (Assignment n)) (C D : ProperClause n k)
    (F : Formula n k m) : insertionDelay k (m + 1) S C (Fin.cons D F) =
      alive S - alive (addClause S C) + insertionDelay k m (addClause S D) C F := by
  simp only [insertionDelay, lifetime_cons, addClause_comm S C D]
  ring

theorem pivot_sq {n k : ℕ} (S : Finset (Assignment n)) (C : ProperClause n k) :
    (alive S - alive (addClause S C)) ^ 2 = alive S - alive (addClause S C) := by
  have hsub := alive_mono (addClause_subset S C)
  unfold alive at hsub ⊢
  split_ifs at hsub ⊢ <;> norm_num at *

theorem insertionDelay_cross {n k m : ℕ} {S T : Finset (Assignment n)} (hTS : T ⊆ S)
    (C : ProperClause n k) (F : Formula n k m) :
    (alive S - alive (addClause S C)) * insertionDelay k m T C F =
      (alive S - alive (addClause S C)) * (alive T + lifetime k m T F) := by
  by_cases hzero : alive S - alive (addClause S C) = 0
  · rw [hzero, zero_mul, zero_mul]
  · have he : addClause S C = ∅ := by
      by_contra hn
      have hSC := Finset.nonempty_iff_ne_empty.mpr hn
      have hS := hSC.mono (addClause_subset S C)
      simp [alive, hSC, hS] at hzero
    have hf : addClause T C = ∅ := Finset.subset_empty.mp (by
      rw [← he]
      exact addClause_mono hTS C)
    simp [insertionDelay, hf]

theorem insertionDelay_cons_sq {n k m : ℕ} (S : Finset (Assignment n)) (C D : ProperClause n k)
    (F : Formula n k m) : insertionDelay k (m + 1) S C (Fin.cons D F) ^ 2 =
      insertionDelay k m (addClause S D) C F ^ 2 + (alive S - alive (addClause S C)) +
      2 * (alive S - alive (addClause S C)) *
        (alive (addClause S D) + lifetime k m (addClause S D) F) := by
  rw [insertionDelay_cons]
  have h := insertionDelay_cross (addClause_subset S D) C F
  have hs := pivot_sq S C
  nlinarith [hs, h]

theorem insertionSecond_zero {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    insertionSecond k 0 S = killingChance k S := by
  rw [killingChance_eq_mean hkn]
  unfold insertionSecond
  apply uniformMean_congr
  intro C
  simp only [insertionDelay_zero, pivot_sq, uniformMean_const]

theorem insertionSecond_succ {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    insertionSecond k (m + 1) S = clauseAverage k (insertionSecond k m) S +
      killingChance k S * (1 + 2 * lifetimeMean k (m + 1) S) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  unfold insertionSecond
  simp_rw [uniformMean_fin_succ, insertionDelay_cons_sq, uniformMean_add,
    uniformMean_const_mul, uniformMean_const]
  rw [uniformMean_comm (fun C D => uniformMean
    (fun F : Formula n k m => insertionDelay k m (addClause S D) C F ^ 2))]
  rw [← killingChance_eq_mean hkn]
  have hmean : (uniformMean fun D : ProperClause n k =>
      alive (addClause S D) + uniformMean (lifetime k m (addClause S D))) =
      lifetimeMean k (m + 1) S := (lifetimeMean_succ hkn S).symm
  simp_rw [uniformMean_add, uniformMean_const]
  simp only [uniformMean_add] at hmean
  rw [hmean]
  simp only [uniformMean_mul_const, uniformMean_const_mul,
    ← killingChance_eq_mean hkn]
  dsimp only [clauseAverage]
  ring

theorem killing_geometric_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (t : ℕ) :
    q * ∑ j ∈ Finset.range t, (1 - q)^j ≤ min ((t : ℝ) * q) 1 := by
  have hgeom : q * ∑ j ∈ Finset.range t, (1 - q)^j = 1 - (1 - q)^t := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  apply le_min
  · calc
      _ ≤ q * ∑ _j ∈ Finset.range t, (1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
          pow_le_one₀ (by linarith) (by linarith))) hq0
      _ = _ := by simp; ring
  · rw [hgeom]
    linarith [pow_nonneg (sub_nonneg.mpr hq1) t]

theorem pivotal_local_bound {n k m M : ℕ} (hkn : k ≤ n) (hm : m + 1 ≤ M)
    (S : Finset (Assignment n)) :
    killingChance k S * (1 + 2 * lifetimeMean k m S) ≤ 2 * truncatedKilling k M S := by
  have hq0 := killingChance_nonneg hkn S
  have hq1 := killingChance_le_one (k := k) S
  have hsum : 1 + lifetimeMean k m S ≤
      ∑ j ∈ Finset.range (m + 1), (1 - killingChance k S)^j := by
    rw [lifetimeMean_eq_sum hkn, Finset.sum_range_succ']
    simp only [pow_zero]
    simpa only [add_comm] using add_le_add_left
      (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range m) =>
        survival_le_geometric (d := j + 1) hkn S)) 1
  have hgeom := killing_geometric_sum hq0 hq1 (m + 1)
  have hmin : min (((m + 1 : ℕ) : ℝ) * killingChance k S) 1 ≤ truncatedKilling k M S := by
    exact min_le_min (mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hq0) le_rfl
  have hh := mul_le_mul_of_nonneg_left hsum hq0
  nlinarith

theorem occupation_eq_sum {n k m : ℕ} (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    occupation k f m S = ∑ j ∈ Finset.range m, ((clauseAverage k)^[j] f) S := by
  induction m generalizing S with
  | zero => simp [occupation]
  | succ m ih =>
    simp only [occupation]
    have he : occupation k f m = fun T => ∑ j ∈ Finset.range m, ((clauseAverage k)^[j] f) T :=
      funext ih
    rw [he, clauseAverage_sum, Finset.sum_range_succ']
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id_eq]
    ring

theorem insertionSecond_le_occupation {n k m M : ℕ} (hkn : k ≤ n) (hm : m + 1 ≤ M)
    (S : Finset (Assignment n)) :
    insertionSecond k m S ≤ 2 * occupation k (truncatedKilling k M) (m + 1) S := by
  induction m generalizing S with
  | zero =>
    rw [insertionSecond_zero hkn]
    have hp := pivotal_local_bound (m := 0) hkn hm S
    simpa [occupation, clauseAverage, uniformMean_zero, lifetimeMean, lifetime, uniformMean] using hp
  | succ m ih =>
    rw [insertionSecond_succ hkn, occupation]
    have hp := pivotal_local_bound (m := m + 1) hkn hm S
    have havg := clauseAverage_mono (k := k) (fun T => ih (by omega) T) S
    change clauseAverage k (insertionSecond k m) S ≤
      uniformMean (fun C : ProperClause n k => 2 * occupation k (truncatedKilling k M) (m + 1)
        (addClause S C)) at havg
    rw [uniformMean_const_mul] at havg
    change clauseAverage k (insertionSecond k m) S ≤
      2 * clauseAverage k (occupation k (truncatedKilling k M) (m + 1)) S at havg
    linarith

theorem uniformVariance_const_add {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (c : ℝ) : uniformVariance (fun a => c + f a) = uniformVariance f := by
  unfold uniformVariance
  rw [uniformMean_add, uniformMean_const]
  apply uniformMean_congr
  intro a
  congr 1
  ring

theorem uniformVariance_fin_succ {α : Type*} [Fintype α] [Nonempty α] {m : ℕ}
    (f : (Fin (m + 1) → α) → ℝ) :
    uniformVariance f = uniformMean (fun C => uniformVariance (fun F : Fin m → α =>
      f (Fin.cons C F))) + uniformVariance (fun C => uniformMean (fun F : Fin m → α =>
      f (Fin.cons C F))) := by
  simp only [uniformVariance_eq, uniformMean_fin_succ, uniformMean_sub]
  ring

theorem lifetimeVariance_succ_le {n k m : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    lifetimeVariance k (m + 1) S ≤
      clauseAverage k (lifetimeVariance k m) S + insertionSecond k m S := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  unfold lifetimeVariance
  rw [uniformVariance_fin_succ]
  simp only [lifetime_cons, uniformVariance_const_add]
  apply add_le_add le_rfl
  let c := alive S + lifetimeMean k m S
  calc
    _ ≤ uniformMean (fun C : ProperClause n k =>
        (uniformMean (fun F : Formula n k m =>
          alive (addClause S C) + lifetime k m (addClause S C) F) - c)^2) :=
        uniformVariance_le_sq_dist _ c
    _ ≤ insertionSecond k m S := by
      apply uniformMean_mono
      intro C
      have h := uniformMean_sq_ge (fun F : Formula n k m => insertionDelay k m S C F)
      have he : uniformMean (fun F : Formula n k m => insertionDelay k m S C F) =
          c - uniformMean (fun F : Formula n k m =>
            alive (addClause S C) + lifetime k m (addClause S C) F) := by
        simp only [insertionDelay, uniformMean_sub, uniformMean_add, uniformMean_const,
          c, lifetimeMean]
      rw [he] at h
      nlinarith

theorem clauseAverage_const_mul {n k : ℕ} (c : ℝ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    clauseAverage k (fun T => c * f T) S = c * clauseAverage k f S :=
  uniformMean_const_mul c _

theorem lifetimeVariance_le_occupation {n k m M : ℕ} (hkn : k ≤ n) (hm : m ≤ M)
    (S : Finset (Assignment n)) :
    lifetimeVariance k m S ≤ 2 * m * occupation k (truncatedKilling k M) m S := by
  induction m generalizing S with
  | zero => simp [lifetimeVariance, lifetime, uniformVariance, uniformMean]
  | succ m ih =>
    have hv := lifetimeVariance_succ_le (m := m) hkn S
    have hi := insertionSecond_le_occupation hkn hm S
    have havg := clauseAverage_mono (k := k) (fun T => ih (by omega) T) S
    rw [clauseAverage_const_mul] at havg
    have hq : 0 ≤ truncatedKilling k M S :=
      le_min (mul_nonneg (Nat.cast_nonneg _) (killingChance_nonneg hkn S)) zero_le_one
    have he : occupation k (truncatedKilling k M) (m + 1) S =
        truncatedKilling k M S + clauseAverage k (occupation k (truncatedKilling k M) m) S := rfl
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hq]

theorem killingChance_eq_killingProbability {n k : ℕ} (hkn : k ≤ n)
    (S : Finset (Assignment n)) : killingChance k S = killingProbability k S := by
  by_cases hS : S.Nonempty
  · rw [killingChance_eq_probability hkn hS]
    simp [killingProbability, hS]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [killingChance]

theorem forcedFraction_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ forcedFraction S := by
  unfold forcedFraction
  positivity

theorem killingChance_le_forced_pow {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (S : Finset (Assignment n)) : killingChance k S ≤ forcedFraction S ^ k := by
  rw [killingChance_eq_killingProbability hkn, killingProbability_eq hk]
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hbn : (forcedVariables S).card ≤ n := by simpa using Finset.card_le_univ (forcedVariables S)
  have h := killFraction_le_pow hbn hkn hn
  apply h.trans
  apply pow_le_pow_left₀ (by positivity)
  unfold forcedFraction
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hn)
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem truncatedKilling_le_forced {n k M : ℕ} {L : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (hL : 1 ≤ L) (hM : (M : ℝ) ≤ L * n)
    (S : Finset (Assignment n)) :
    truncatedKilling k M S ≤ L * replacementScale n k * forcedFraction S := by
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have ha := replacementScale_pos (k := k) hn
  have hr := forcedFraction_nonneg S
  have ht : 0 ≤ replacementScale n k * forcedFraction S := mul_nonneg ha.le hr
  by_cases hsmall : replacementScale n k * forcedFraction S ≤ 1
  · calc
      truncatedKilling k M S ≤ (M : ℝ) * killingChance k S := min_le_left _ _
      _ ≤ (L * n) * forcedFraction S ^ k :=
        mul_le_mul hM (killingChance_le_forced_pow hk hkn S)
          (killingChance_nonneg hkn S) (by positivity)
      _ = L * (replacementScale n k * forcedFraction S)^k := by
        rw [mul_pow, replacementScale_pow hn hk]
        ring
      _ ≤ L * (replacementScale n k * forcedFraction S) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have he : (replacementScale n k * forcedFraction S)^k =
            (replacementScale n k * forcedFraction S)^(k - 1) *
              (replacementScale n k * forcedFraction S) := by
          rw [← pow_succ, Nat.sub_add_cancel hk]
        rw [he]
        exact mul_le_of_le_one_left ht (pow_le_one₀ ht hsmall)
      _ = _ := by ring
  · calc
      truncatedKilling k M S ≤ 1 := min_le_right _ _
      _ ≤ L * (replacementScale n k * forcedFraction S) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hL) ht]
      _ = _ := by ring

theorem clauseAverage_iterate_eq_mean {n k m : ℕ} (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    ((clauseAverage k)^[m] f) S = uniformMean (fun F : Formula n k m =>
      f (restrictSolutions S F)) := by
  induction m generalizing S with
  | zero =>
    simp only [Function.iterate_zero, id_eq, restrictSolutions_zero, uniformMean_const]
  | succ m ih =>
    rw [Function.iterate_succ_apply', uniformMean_fin_succ]
    change uniformMean (fun C : ProperClause n k =>
      ((clauseAverage k)^[m] f) (addClause S C)) = _
    apply uniformMean_congr
    intro C
    rw [ih]
    apply uniformMean_congr
    intro F
    rw [restrictSolutions_cons]

theorem occupation_forced_eq {n k m : ℕ} :
    occupation k (forcedFraction (n := n)) m Finset.univ =
      ∑ j ∈ Finset.range m, forcedFractionMean n k j := by
  rw [occupation_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact clauseAverage_iterate_eq_mean _ _

theorem occupation_mono {n k m : ℕ} {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) (S : Finset (Assignment n)) :
    occupation k f m S ≤ occupation k g m S := by
  rw [occupation_eq_sum, occupation_eq_sum]
  exact Finset.sum_le_sum fun _ _ => clauseAverage_iterate_mono hfg S

theorem occupation_const_mul {n k m : ℕ} (c : ℝ) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) :
    occupation k (fun T => c * f T) m S = c * occupation k f m S := by
  induction m generalizing S with
  | zero => simp [occupation]
  | succ m ih =>
    simp only [occupation]
    have he : occupation k (fun T => c * f T) m = fun T => c * occupation k f m T := funext ih
    rw [he, clauseAverage_const_mul]
    ring

theorem lifetimeVariance_forcing_bound {n k M : ℕ} {L : ℝ}
    (hk : 0 < k) (hkn : k ≤ n) (hL : 1 ≤ L) (hM : (M : ℝ) ≤ L * n) :
    lifetimeVariance k M (Finset.univ : Finset (Assignment n)) ≤
      (2 * M * L * replacementScale n k) *
        ∑ j ∈ Finset.range M, forcedFractionMean n k j := by
  have hv := lifetimeVariance_le_occupation hkn (le_refl M) (Finset.univ : Finset (Assignment n))
  have ho := occupation_mono (k := k) (m := M)
    (fun S => truncatedKilling_le_forced hk hkn hL hM S) Finset.univ
  rw [occupation_const_mul, occupation_forced_eq] at ho
  have hmul := mul_le_mul_of_nonneg_left ho (by positivity : (0 : ℝ) ≤ 2 * M)
  nlinarith

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Concentration
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Normalized capped centers and polynomial concentration of the proper-clause
satisfiability probability.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem capMultiplier_pos (k : ℕ) : 0 < capMultiplier k := by
  unfold capMultiplier
  positivity

theorem replacementBlock_le {n k : ℕ} (hn : 1 ≤ n) :
    (replacementBlock n k : ℝ) ≤ (2 * k + 1) * replacementScale n k := by
  have ha := replacementScale_one_le (k := k) hn
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * (k : ℝ) * replacementScale n k by positivity)
  change (replacementBlock n k : ℝ) < 2 * k * replacementScale n k + 1 at hc
  nlinarith

theorem replacementError_mul {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (n : ℝ) * replacementError n k = replacementScale n k := by
  have ha := replacementScale_pos (k := k) hn
  have hp : replacementScale n k ^ (k - 1) * replacementScale n k = (n : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel hk, replacementScale_pow hn hk]
  unfold replacementError
  rw [inv_pow]
  rw [mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ (ne_of_gt ha))]
  nlinarith [hp]

theorem integrated_forcing_capped {n k L : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    ∑ j ∈ Finset.range (L * n), forcedFractionMean n k j ≤
      ((L : ℝ) * k * (2 * k + L + 2)) * replacementScale n k := by
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have h := integrated_forcing_finite hk hn (L * n)
  have hpartial : (∑ j ∈ Finset.range (L * n), forcedFractionMean n k j) ≤
      ∑ j ∈ Finset.range (L * n + 1), forcedFractionMean n k j := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (uniformMean_nonneg (fun _ => by positivity))
  have heps := replacementError_mul (k := k) hn0 (by omega)
  have hg := replacementBlock_le (k := k) (by omega : 1 ≤ n)
  have ha := replacementScale_pos (k := k) hn0
  have he0 := replacementError_nonneg n k
  have hclean : (replacementBlock n k : ℝ) * ((L * n : ℕ) : ℝ) * ((k : ℝ) / n) +
      ((L * n + 1 : ℕ) : ℝ) * ((L * n : ℕ) : ℝ) * ((k : ℝ) / n) * replacementError n k =
      (L : ℝ) * k * replacementBlock n k +
        ((L : ℝ) * n + 1) * L * k * replacementError n k := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    field_simp
  rw [hclean] at h
  have he : replacementError n k ≤ replacementScale n k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn1) he0]
  have hg' := mul_le_mul_of_nonneg_left hg (by positivity : (0 : ℝ) ≤ L * k)
  have he' := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ L * k)
  have hp : ((L : ℝ) * n + 1) * L * k * replacementError n k =
      (L : ℝ)^2 * k * replacementScale n k + L * k * replacementError n k := by
    nlinarith [congrArg (fun x : ℝ => (L : ℝ)^2 * k * x) heps]
  rw [hp] at h
  nlinarith

theorem variance_capped {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    lifetimeVariance k (mainCap n k) (Finset.univ : Finset (Assignment n)) ≤
      varianceConstant k * n * replacementScale n k ^ 2 := by
  have hL : (1 : ℝ) ≤ capMultiplier k := by exact_mod_cast capMultiplier_pos k
  have hv := lifetimeVariance_forcing_bound (n := n) (k := k) (M := mainCap n k)
    (L := capMultiplier k) (by omega) (by omega) hL (by simp [mainCap])
  have hf := integrated_forcing_capped (L := capMultiplier k) hk hn
  have hmul := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ 2 * (mainCap n k : ℝ) * capMultiplier k * replacementScale n k by
      have ha := replacementScale_pos (k := k) (by omega : 0 < n)
      positivity)
  apply hv.trans
  exact hmul.trans_eq (by simp only [mainCap, Nat.cast_mul, varianceConstant]; ring)

theorem uniform_chebyshev {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {t : ℝ} (ht : 0 < t) :
    uniformProbability (fun a => t ≤ |f a - uniformMean f|) ≤ uniformVariance f / t^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos ht), uniformProbability_eq_mean, ← uniformMean_mul_const]
  apply uniformMean_mono
  intro a
  by_cases h : t ≤ |f a - uniformMean f|
  · simp only [ite_eq_left h, one_mul]
    nlinarith [sq_abs (f a - uniformMean f)]
  · simp only [ite_eq_right h, zero_mul]
    exact sq_nonneg _

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

theorem variance_window_identity {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (n : ℝ) * replacementScale n k ^ 2 =
      fluctuationWindow n k ^ 2 * (n : ℝ)^(-eta k) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hexp : 1 + (1 / (k : ℝ)) * 2 = (1 - delta k) * 2 + -eta k := by
    unfold delta eta
    field_simp
    ring
  calc
    _ = (n : ℝ)^(1 + (1 / (k : ℝ)) * 2) := by
      rw [Real.rpow_add hn', Real.rpow_one, Real.rpow_mul hn'.le, Real.rpow_two]
      rfl
    _ = (n : ℝ)^((1 - delta k) * 2 + -eta k) := by rw [hexp]
    _ = _ := by
      rw [Real.rpow_add hn', Real.rpow_mul hn'.le, Real.rpow_two]
      rfl

theorem concentration_capped {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    uniformProbability (fun F : Formula n k (mainCap n k) =>
      fluctuationWindow n k ≤ |lifetime k (mainCap n k) Finset.univ F -
        (n : ℝ) * center n k|) ≤ concentrationError n k := by
  let : Nonempty (ProperClause n k) := nonempty_properClause (by omega)
  have hn0 : 0 < n := by omega
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn0
  have hm : (n : ℝ) * center n k = lifetimeMean k (mainCap n k) (Finset.univ : Finset (Assignment n)) := by
    unfold center
    field_simp
  rw [hm]
  have h := uniform_chebyshev (lifetime k (mainCap n k) (Finset.univ : Finset (Assignment n)))
    (fluctuationWindow_pos (k := k) hn0)
  apply h.trans
  have hv := div_le_div_of_nonneg_right (variance_capped hk hn)
    (sq_nonneg (fluctuationWindow n k))
  apply hv.trans_eq
  have hid := variance_window_identity (k := k) hn0 (by omega)
  unfold concentrationError
  calc
    _ = varianceConstant k * ((n : ℝ) * replacementScale n k^2) / fluctuationWindow n k^2 := by ring
    _ = _ := by
      rw [hid]
      field_simp [ne_of_gt (fluctuationWindow_pos (k := k) hn0)]

theorem properSATProbability_center_lower_sat_oai {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
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
end

theorem solution : type_of% @OAI.FixedClauseThreshold.properSATProbability_center_lower_sat_oai := @OAI.FixedClauseThreshold.properSATProbability_center_lower_sat_oai
