-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:48:53.908923+00:00
-- url     : https://prove2.me/submissions/62773a58-2267-438a-9336-c0e56be8342c

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_threshold_program_sat
import Theorems.Thm_OAI_FixedClauseThreshold_auxiliaryProbability_center_lower_sat
import Theorems.Thm_OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability_sat
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_lt_cap_sat
import Theorems.Thm_OAI_FixedClauseThreshold_limitingCenter_pos_sat
import Theorems.Thm_OAI_FixedClauseThreshold_properSATProbability_center_upper_sat
import Theorems.Thm_OAI_FixedClauseThreshold_subcritical_limit_sat

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

theorem uniformProbability_nonneg {α : Type*} [Fintype α] (p : α → Prop) :
    0 ≤ uniformProbability p := by
  unfold uniformProbability
  positivity

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
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Replacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem binomialMean_id (p : ℝ) (m : ℕ) :
    binomialMean p m (fun d => (d : ℝ)) = (m : ℝ) * p := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    simp only [binomialMean, Nat.cast_add, Nat.cast_one, binomialMean_add,
      binomialMean_const, ih]
    ring

theorem uniformMean_binomialMean {α : Type*} [Fintype α]
    (p : ℝ) (m : ℕ) (f : ℕ → α → ℝ) :
    uniformMean (fun a => binomialMean p m (fun d => f d a)) =
      binomialMean p m (fun d => uniformMean (f d)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [binomialMean, uniformMean_add, uniformMean_const_mul, ih]

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

@[simp] theorem survival_empty {n k m : ℕ} : survival k m (∅ : Finset (Assignment n)) = 0 := by
  rw [survival_eq_mean]
  have h (F : Formula n k m) : restrictSolutions ∅ F = ∅ := by simp [restrictSolutions]
  simp only [h, alive_empty, uniformMean_zero]

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

theorem alive_univ (n : ℕ) : alive (Finset.univ : Finset (Assignment n)) = 1 := by
  simp [alive]

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

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterBounds
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableSatisfiability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite union bounds, a matching criterion for satisfiability, and positive finite
bounds for the normalized centers.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformProbability_exists_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) :
    uniformProbability (fun a => ∃ b, p a b) ≤ ∑ b, uniformProbability (fun a => p a b) := by
  simp only [uniformProbability_eq_mean]
  rw [← uniformMean_sum]
  apply uniformMean_mono
  intro a
  by_cases h : ∃ b, p a b
  · obtain ⟨b, hb⟩ := h
    rw [ite_eq_left ⟨b, hb⟩]
    calc
      1 = (if p a b then (1 : ℝ) else 0) := (ite_eq_left hb).symm
      _ ≤ ∑ b, if p a b then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun b => if p a b then (1 : ℝ) else 0)
          (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ b)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun b _ => by split_ifs <;> norm_num)

theorem uniformProbability_forall_fintype {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ b, p (f b)) = uniformProbability p ^ Fintype.card β := by
  unfold uniformProbability
  have hc : Fintype.card {f : β → α // ∀ b, p (f b)} =
      Fintype.card (β → {a : α // p a}) :=
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun _ : β => p))
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow, div_pow]

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

theorem satisfiable_of_matching {n k m : ℕ} (F : Formula n k m)
    (f : Fin m → Fin n) (hf : Function.Injective f)
    (hmem : ∀ j, f j ∈ clauseSupport (F j)) : Satisfiable F := by
  let b : Fin m → Bool := fun j => ((F j).val (f j)).getD false
  let σ : Assignment n := fun i => if h : ∃ j, f j = i then b (Classical.choose h) else false
  refine ⟨σ, fun j => ⟨f j, ?_⟩⟩
  have he : ∃ j', f j' = f j := ⟨j, rfl⟩
  have hc : Classical.choose he = j := hf (Classical.choose_spec he)
  have hs : σ (f j) = b j := by simp [σ, he, hc]
  rw [hs]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp ((mem_clauseSupport _ _).mp (hmem j))
  simp [b, hv]

theorem unsatisfiable_deficiency {n k m : ℕ} (F : Formula n k m) (hF : ¬Satisfiable F) :
    ∃ J : Finset (Fin m), (J.biUnion fun j => clauseSupport (F j)).card < J.card := by
  by_contra h
  push Not at h
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective (fun j => clauseSupport (F j))).mp h
  exact hF (satisfiable_of_matching F f hf hmem)

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

theorem uniformProbability_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : β → Prop) :
    uniformProbability (fun a => p (e a)) = uniformProbability p := by
  unfold uniformProbability
  rw [Fintype.card_congr (Equiv.subtypeEquiv e (fun _ => Iff.rfl)), Fintype.card_congr e]

theorem uniformProbability_prod_first {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (p : α → Prop) : uniformProbability (fun x : α × β => p x.1) = uniformProbability p := by
  let e : {x : α × β // p x.1} ≃ {a : α // p a} × β := {
    toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
    invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.cast_mul, Nat.cast_mul]
  have hb : (Nat.card β : ℝ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero (α := β)
  field_simp

theorem uniformProbability_forall_mem {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]
    (J : Finset β) (p : α → Prop) :
    uniformProbability (fun f : β → α => ∀ j ∈ J, p (f j)) = uniformProbability p ^ J.card := by
  let e := Equiv.piEquivPiSubtypeProd (fun j => j ∈ J) (fun _ : β => α)
  calc
    _ = uniformProbability (fun f : β → α => ∀ j : ↥J, p ((e f).1 j)) :=
      uniformProbability_congr (fun f => by simp [e])
    _ = uniformProbability (fun f : (↥J → α) × ({j : β // j ∉ J} → α) =>
        ∀ j, p (f.1 j)) := uniformProbability_equiv
          (α := β → α) (β := (↥J → α) × ({j : β // j ∉ J} → α)) e
          (fun f => ∀ j, p (f.1 j))
    _ = uniformProbability (fun f : ↥J → α => ∀ j, p (f j)) :=
      uniformProbability_prod_first (α := ↥J → α) (β := {j : β // j ∉ J} → α)
        (fun f : ↥J → α => ∀ j, p (f j))
    _ = _ := by
      have h := uniformProbability_forall_fintype (α := α) (β := ↥J) p
      simpa only [Fintype.card_coe] using h

theorem uniformMean_support {n k : ℕ} (f : Finset (Fin n) → ℝ) :
    uniformMean (fun C : ProperClause n k => f (clauseSupport C)) =
      uniformMean (fun s : VariableSet n k => f s.val) := by
  have he := uniformMean_equiv (properClauseEquiv n k) (fun s => f s.1.val)
  change uniformMean (fun C : ProperClause n k => f (clauseSupport C)) = _ at he
  rw [he]
  have hc (s : VariableSet n k) : Fintype.card (↥s.val → Bool) = 2^k := by
    simp [(Finset.mem_powersetCard.mp s.property).2]
  simp only [uniformMean, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Fintype.card_sigma, hc, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  have h2 : (2 : ℝ)^k ≠ 0 := by positivity
  push_cast
  field_simp

theorem uniformProbability_support_subset {n k : ℕ} (T : Finset (Fin n)) :
    uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) =
      (T.card.choose k : ℝ) / n.choose k := by
  have hm := uniformMean_support (k := k) (fun S => if S ⊆ T then (1 : ℝ) else 0)
  have hp : uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) =
      uniformProbability (fun s : VariableSet n k => s.val ⊆ T) := by
    rw [uniformProbability_eq_mean, uniformProbability_eq_mean]
    calc
      _ = uniformMean (fun C : ProperClause n k =>
          if clauseSupport C ⊆ T then (1 : ℝ) else 0) := by
            apply uniformMean_congr
            intro C
            by_cases h : clauseSupport C ⊆ T <;> simp only [h, ite_true, ite_false]
      _ = _ := hm
      _ = _ := by
        apply uniformMean_congr
        intro C
        by_cases h : C.val ⊆ T <;> simp only [h, ite_true, ite_false]
  rw [hp]
  let e : {s : VariableSet n k // s.val ⊆ T} ≃ ↥(T.powersetCard k) := {
    toFun := fun s => ⟨s.val.val, Finset.mem_powersetCard.mpr
      ⟨s.property, (Finset.mem_powersetCard.mp s.val.property).2⟩⟩
    invFun := fun s => ⟨⟨s.val, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp s.property).2⟩⟩,
        (Finset.mem_powersetCard.mp s.property).1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem choose_quotient_le_pow {b n k : ℕ} (hbn : b ≤ n) (hkn : k ≤ n) (hn : 0 < n) :
    (b.choose k : ℝ) / n.choose k ≤ ((b : ℝ) / n)^k := by
  have h := mul_le_mul_of_nonneg_right (killFraction_le_pow hbn hkn hn)
    (by positivity : (0 : ℝ) ≤ 2^k)
  have h2 : (2 : ℝ)^k ≠ 0 := by positivity
  calc
    _ = killFraction b n k * 2^k := by
      unfold killFraction
      field_simp
    _ ≤ ((b : ℝ) / (2 * n))^k * 2^k := h
    _ = _ := by
      rw [← mul_pow]
      congr 1
      field_simp

theorem clause_subset_bound {n k : ℕ} (hkn : k ≤ n) (hn : 0 < n) (T : Finset (Fin n)) :
    uniformProbability (fun C : ProperClause n k => clauseSupport C ⊆ T) ≤
      ((T.card : ℝ) / n)^k := by
  rw [uniformProbability_support_subset]
  exact choose_quotient_le_pow (by simpa using Finset.card_le_univ T) hkn hn

theorem unsatisfiable_container {n k m : ℕ} (hmn : m ≤ n) (F : Formula n k m)
    (hF : ¬Satisfiable F) :
    ∃ t : Fin m, ∃ J : VariableSet m (t.val + 1), ∃ T : VariableSet n (t.val + 1),
      ∀ j ∈ J.val, clauseSupport (F j) ⊆ T.val := by
  obtain ⟨J, hdef⟩ := unsatisfiable_deficiency F hF
  have ht : 0 < J.card := lt_of_le_of_lt (Nat.zero_le _) hdef
  have htm : J.card ≤ m := by simpa using Finset.card_le_univ J
  obtain ⟨T, hUT, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (J.biUnion fun j => clauseSupport (F j))) hdef.le
      (show J.card ≤ (Finset.univ : Finset (Fin n)).card by simpa using htm.trans hmn)
  have hts : J.card - 1 + 1 = J.card := Nat.sub_add_cancel ht
  refine ⟨⟨J.card - 1, by omega⟩,
    ⟨J, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hts.symm⟩⟩,
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT.trans hts.symm⟩⟩, ?_⟩
  intro j hj i hi
  exact hUT (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)

theorem deficiency_union_bound {n k m : ℕ} (hkn : k ≤ n) (hn : 0 < n) (hmn : m ≤ n) :
    1 - properSATProbability n k m ≤
      ∑ t ∈ Finset.range m, (m.choose (t + 1) : ℝ) * n.choose (t + 1) *
        (((t + 1 : ℕ) : ℝ) / n)^(k * (t + 1)) := by
  let : Nonempty (ProperClause n k) := nonempty_properClause hkn
  let E (F : Formula n k m) (t : Fin m) (J : VariableSet m (t.val + 1))
      (T : VariableSet n (t.val + 1)) : Prop := ∀ j ∈ J.val, clauseSupport (F j) ⊆ T.val
  have hsat : 1 - properSATProbability n k m =
      uniformProbability (fun F : Formula n k m => ¬Satisfiable F) :=
    (uniformProbability_not (fun F : Formula n k m => Satisfiable F)).symm
  have hE (t : Fin m) (J : VariableSet m (t.val + 1)) (T : VariableSet n (t.val + 1)) :
      uniformProbability (fun F : Formula n k m => E F t J T) ≤
        (((t.val + 1 : ℕ) : ℝ) / n)^(k * (t.val + 1)) := by
    dsimp [E]
    rw [uniformProbability_forall_mem (α := ProperClause n k) (β := Fin m) J.val
      (fun C => clauseSupport C ⊆ T.val)]
    have ht := (Finset.mem_powersetCard.mp T.property).2
    have hj := (Finset.mem_powersetCard.mp J.property).2
    rw [hj]
    have h := pow_le_pow_left₀ (uniformProbability_nonneg _)
      (clause_subset_bound hkn hn T.val) (t.val + 1)
    rwa [ht, ← pow_mul] at h
  rw [hsat]
  calc
    _ ≤ uniformProbability (fun F : Formula n k m => ∃ t, ∃ J, ∃ T, E F t J T) :=
      uniformProbability_mono (fun F hF => unsatisfiable_container hmn F hF)
    _ ≤ ∑ t : Fin m, uniformProbability (fun F : Formula n k m => ∃ J, ∃ T, E F t J T) :=
      uniformProbability_exists_le _
    _ ≤ ∑ t : Fin m, ∑ J : VariableSet m (t.val + 1),
        ∑ T : VariableSet n (t.val + 1),
          uniformProbability (fun F : Formula n k m => E F t J T) := by
      apply Finset.sum_le_sum
      intro t _
      apply (uniformProbability_exists_le _).trans
      apply Finset.sum_le_sum
      intro J _
      exact uniformProbability_exists_le _
    _ ≤ ∑ t : Fin m, ∑ _ : VariableSet m (t.val + 1), ∑ _ : VariableSet n (t.val + 1),
        (((t.val + 1 : ℕ) : ℝ) / n)^(k * (t.val + 1)) := by
      gcongr with t _ J _ T _
      exact hE t J T
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_variableSet, nsmul_eq_mul]
      simp only [← mul_assoc]
      exact Fin.sum_univ_eq_sum_range (fun t => (m.choose (t+1) : ℝ) * n.choose (t+1) *
        (((t+1 : ℕ) : ℝ) / n)^(k*(t+1))) m

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

theorem lowerCenterBound_pos : 0 < lowerCenterBound := div_pos smallDensity_pos (by norm_num)

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
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Interpolation
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem finiteClauseAverage_add {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f g : Finset (Assignment n) → ℝ) :
    finiteClauseAverage sat (fun S => f S + g S) =
      (fun S => finiteClauseAverage sat f S + finiteClauseAverage sat g S) := by
  funext S
  exact uniformMean_add _ _

theorem finiteClauseAverage_const_mul {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    finiteClauseAverage sat (fun S => c * f S) = (fun S => c * finiteClauseAverage sat f S) := by
  funext S
  exact uniformMean_const_mul _ _

theorem finiteClauseAverage_commute {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop) :
    Function.Commute (finiteClauseAverage satC) (finiteClauseAverage satD) := by
  intro f
  funext S
  unfold finiteClauseAverage
  rw [uniformMean_comm]
  apply uniformMean_congr
  intro d
  apply uniformMean_congr
  intro c
  congr 1
  ext σ
  simp only [Finset.mem_filter]
  tauto

theorem finiteClauseAverage_binomialMean {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (p : ℝ) (m : ℕ)
    (f : ℕ → Finset (Assignment n) → ℝ) :
    finiteClauseAverage sat (fun S => binomialMean p m (fun j => f j S)) =
      (fun S => binomialMean p m (fun j => finiteClauseAverage sat (f j) S)) := by
  funext S
  exact uniformMean_binomialMean _ _ _

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

theorem mixedAverage_mono {X : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : (X → ℝ) → (X → ℝ)} (hA : Monotone A) (hB : Monotone B) :
    Monotone (mixedAverage p A B) := by
  intro f g hfg S
  exact add_le_add (mul_le_mul_of_nonneg_left (hB hfg S) (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left (hA hfg S) hp0)

theorem finiteClauseAverage_commute_mix {n : ℕ} {C D E : Type*}
    [Fintype C] [Fintype D] [Fintype E] (satC : C → Assignment n → Prop)
    (satD : D → Assignment n → Prop) (satE : E → Assignment n → Prop) (p : ℝ) :
    Function.Commute (finiteClauseAverage satC)
      (mixedAverage p (finiteClauseAverage satD) (finiteClauseAverage satE)) := by
  intro f
  unfold mixedAverage
  rw [finiteClauseAverage_add, finiteClauseAverage_const_mul, finiteClauseAverage_const_mul,
    finiteClauseAverage_commute satC satD f, finiteClauseAverage_commute satC satE f]

theorem opposing_literal_iff {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n)
    (σ₀ : Assignment n) (hσ₀ : σ₀ ∈ S) (l : Fin v × Bool) :
    (∀ σ ∈ S, σ (e l.1) ≠ l.2) ↔
      l.1 ∈ embeddedForced S e ∧ l.2 = !(σ₀ (e l.1)) := by
  rw [mem_embeddedForced, forcedVariables_eq_frozen hσ₀]
  simp only [frozenCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have h0 := h σ₀ hσ₀
    constructor
    · intro σ hσ
      have hs := h σ hσ
      cases h1 : σ (e l.1) <;> cases h2 : σ₀ (e l.1) <;> cases h3 : l.2 <;> simp_all
    · cases h2 : σ₀ (e l.1) <;> cases h3 : l.2 <;> simp_all
  · rintro ⟨h, hb⟩ σ hσ
    rw [h σ hσ, hb]
    cases σ₀ (e l.1) <;> decide

theorem opposing_literal_probability {n v : ℕ} (S : Finset (Assignment n))
    (e : Fin v → Fin n) (hS : S.Nonempty) :
    uniformProbability (fun l : Fin v × Bool => ∀ σ ∈ S, σ (e l.1) ≠ l.2) =
      ((embeddedForced S e).card : ℝ) / (2 * v) := by
  obtain ⟨σ₀, hσ₀⟩ := hS
  let eqv : {l : Fin v × Bool // ∀ σ ∈ S, σ (e l.1) ≠ l.2} ≃ ↥(embeddedForced S e) := {
    toFun := fun l => ⟨l.val.1, ((opposing_literal_iff S e σ₀ hσ₀ l.val).mp l.property).1⟩
    invFun := fun i => ⟨(i.val, !(σ₀ (e i.val))),
      (opposing_literal_iff S e σ₀ hσ₀ _).mpr ⟨i.property, rfl⟩⟩
    left_inv := fun l => by
      apply Subtype.ext
      change (l.val.1, !(σ₀ (e l.val.1))) = l.val
      apply Prod.ext
      · rfl
      · exact ((opposing_literal_iff S e σ₀ hσ₀ l.val).mp l.property).2.symm
    right_inv := fun _ => rfl }
  unfold uniformProbability
  simp only [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr eqv]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (v : ℝ) 2]

theorem embedded_kill_probability {n v k : ℕ} (S : Finset (Assignment n))
    (e : Fin v → Fin n) (hS : S.Nonempty) :
    uniformProbability (fun C : AuxiliaryClause v k =>
      ¬ (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty) =
      (((embeddedForced S e).card : ℝ) / (2 * v))^k := by
  calc
    _ = uniformProbability (fun C : AuxiliaryClause v k =>
        ∀ j, ∀ σ ∈ S, σ (e (C j).1) ≠ (C j).2) := by
      apply uniformProbability_congr
      intro C
      constructor
      · intro h j σ hσ heq
        apply h
        exact ⟨σ, Finset.mem_filter.mpr ⟨hσ, ⟨j, heq⟩⟩⟩
      · intro h ⟨σ, hσ⟩
        obtain ⟨hσ, j, hj⟩ := Finset.mem_filter.mp hσ
        exact h j σ hσ hj
    _ = _ := by
      change (uniformProbability (fun C : Fin k → Fin v × Bool =>
        ∀ j, (fun l : Fin v × Bool => ∀ σ ∈ S, σ (e l.1) ≠ l.2) (C j))) = _
      have hf := uniformProbability_forall_fintype (α := Fin v × Bool) (β := Fin k)
        (fun l => ∀ σ ∈ S, σ (e l.1) ≠ l.2)
      simpa only [Fintype.card_fin, opposing_literal_probability S e hS] using hf

theorem embeddedAverage_alive {n v k : ℕ} (hv : 0 < v) (e : Fin v → Fin n)
    (S : Finset (Assignment n)) :
    embeddedAverage e k alive S = alive S *
      (1 - (((embeddedForced S e).card : ℝ) / (2 * v))^k) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  by_cases hS : S.Nonempty
  · have ha : alive S = 1 := by simp [alive, hS]
    rw [ha, one_mul]
    have h := uniformProbability_not (fun C : AuxiliaryClause v k =>
      (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty)
    rw [embedded_kill_probability S e hS] at h
    have he : embeddedAverage e k alive S = uniformProbability (fun C : AuxiliaryClause v k =>
        (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty) := by
      rw [uniformProbability_eq_mean]
      unfold embeddedAverage finiteClauseAverage
      apply uniformMean_congr
      intro C
      by_cases hC : (S.filter fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C)).Nonempty
      · simp only [alive, ite_eq_left hC]
      · simp only [alive, ite_eq_right hC]
    rw [he]
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [embeddedAverage, finiteClauseAverage, alive_empty, uniformMean_zero]

theorem auxiliaryAverage_alive {n k : ℕ} (hn : 0 < n) (S : Finset (Assignment n)) :
    auxiliaryAverage k alive S = alive S * (1 - (forcedFraction S / 2)^k) := by
  rw [auxiliaryAverage, embeddedAverage_alive hn, embeddedForced_id]
  congr 2
  unfold forcedFraction
  ring

theorem forced_card_partition {r s : ℕ} (S : Finset (Assignment (r + s))) :
    (forcedVariables S).card = (embeddedForced S (Fin.castAdd s)).card +
      (embeddedForced S (Fin.natAdd r)).card := by
  have h := Fin.sum_univ_add (fun i : Fin (r + s) =>
    if i ∈ forcedVariables S then (1 : ℕ) else 0)
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_mem_eq_inter, Finset.univ_inter, embeddedForced] using h

theorem partition_kill_convex {r s k : ℕ} (hr : 0 < r) (hs : 0 < s)
    (S : Finset (Assignment (r + s))) :
    (forcedFraction S / 2)^k ≤
      ((r : ℝ) / (r + s)) * (((embeddedForced S (Fin.castAdd s)).card : ℝ) / (2 * r))^k +
      ((s : ℝ) / (r + s)) * (((embeddedForced S (Fin.natAdd r)).card : ℝ) / (2 * s))^k := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : (r : ℝ) / (r + s) + (s : ℝ) / (r + s) = 1 := by field_simp
  have h := (convexOn_pow (𝕜 := ℝ) k).2
    (show ((embeddedForced S (Fin.castAdd s)).card : ℝ) / (2 * r) ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; positivity)
    (show ((embeddedForced S (Fin.natAdd r)).card : ℝ) / (2 * s) ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; positivity)
    (show 0 ≤ (r : ℝ) / (r + s) by positivity)
    (show 0 ≤ (s : ℝ) / (r + s) by positivity) hsum
  simp only [smul_eq_mul] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold forcedFraction
  rw [forced_card_partition, Nat.cast_add, Nat.cast_add]
  field_simp

theorem globalAverage_ge_local {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) :
    mixedAverage ((r : ℝ) / (r + s)) (embeddedAverage (Fin.castAdd s) k)
      (embeddedAverage (Fin.natAdd r) k) alive ≤ auxiliaryAverage k alive := by
  intro S
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hw : 1 - (r : ℝ) / (r + s) = (s : ℝ) / (r + s) := by field_simp; ring
  unfold mixedAverage
  rw [embeddedAverage_alive hr, embeddedAverage_alive hs, auxiliaryAverage_alive (by omega), hw]
  have h := mul_le_mul_of_nonneg_left (partition_kill_convex (k := k) hr hs S) (alive_nonneg S)
  have hsum : (r : ℝ) / (r + s) + (s : ℝ) / (r + s) = 1 := by field_simp
  have hsum_mul := congrArg (fun x : ℝ => alive S * x) hsum
  nlinarith

theorem mixed_finiteAverage_iterate {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop)
    (p : ℝ) (m : ℕ) (f : Finset (Assignment n) → ℝ) :
    (mixedAverage p (finiteClauseAverage satC) (finiteClauseAverage satD))^[m] f =
      (fun S => binomialMean p m (fun j =>
        ((finiteClauseAverage satC)^[j] ((finiteClauseAverage satD)^[m - j] f)) S)) := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold mixedAverage
    rw [finiteClauseAverage_binomialMean, finiteClauseAverage_binomialMean]
    funext S
    rw [binomialMean]
    congr 1
    · congr 1
      apply binomialMean_congr
      intro j hj
      rw [(finiteClauseAverage_commute satD satC).iterate_right j,
        ← Function.iterate_succ_apply' (finiteClauseAverage satD) (m - j) f]
      rw [show (m - j).succ = m.succ - j by omega]
    · congr 1
      apply binomialMean_congr
      intro j hj
      rw [← Function.iterate_succ_apply' (finiteClauseAverage satC) j]
      simp only [Nat.add_sub_add_right]

theorem blockSet_nonempty {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    (blockSet S T).Nonempty ↔ S.Nonempty ∧ T.Nonempty := by
  constructor
  · rintro ⟨σ, hσ⟩
    have h := (mem_blockSet S T σ).mp hσ
    exact ⟨⟨_, h.1⟩, ⟨_, h.2⟩⟩
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨Fin.addCases σ τ, ?_⟩
    simpa only [mem_blockSet, Fin.addCases_left, Fin.addCases_right] using And.intro hσ hτ

theorem alive_blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    alive (blockSet S T) = alive S * alive T := by
  simp only [alive, blockSet_nonempty]
  split_ifs <;> simp_all

theorem filter_blockSet_left {r s k : ℕ} (S : Finset (Assignment r))
    (T : Finset (Assignment s)) (C : AuxiliaryClause r k) :
    (blockSet S T).filter (fun σ => auxiliarySatisfies σ (embedAuxiliaryClause (Fin.castAdd s) C)) =
      blockSet (S.filter (fun σ => auxiliarySatisfies σ C)) T := by
  ext σ
  constructor
  · intro h
    obtain ⟨hσ, hC⟩ := Finset.mem_filter.mp h
    obtain ⟨hS, hT⟩ := (mem_blockSet S T σ).mp hσ
    exact (mem_blockSet _ _ σ).mpr ⟨Finset.mem_filter.mpr ⟨hS, hC⟩, hT⟩
  · intro h
    obtain ⟨hS, hT⟩ := (mem_blockSet _ _ σ).mp h
    obtain ⟨hS, hC⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨(mem_blockSet S T σ).mpr ⟨hS, hT⟩, hC⟩

theorem filter_blockSet_right {r s k : ℕ} (S : Finset (Assignment r))
    (T : Finset (Assignment s)) (C : AuxiliaryClause s k) :
    (blockSet S T).filter (fun σ => auxiliarySatisfies σ (embedAuxiliaryClause (Fin.natAdd r) C)) =
      blockSet S (T.filter (fun σ => auxiliarySatisfies σ C)) := by
  ext σ
  constructor
  · intro h
    obtain ⟨hσ, hC⟩ := Finset.mem_filter.mp h
    obtain ⟨hS, hT⟩ := (mem_blockSet S T σ).mp hσ
    exact (mem_blockSet _ _ σ).mpr ⟨hS, Finset.mem_filter.mpr ⟨hT, hC⟩⟩
  · intro h
    obtain ⟨hS, hT⟩ := (mem_blockSet _ _ σ).mp h
    obtain ⟨hT, hC⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨(mem_blockSet S T σ).mpr ⟨hS, hT⟩, hC⟩

theorem auxiliarySurvival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    auxiliarySurvival k (m + 1) S = uniformMean (fun C : AuxiliaryClause n k =>
      auxiliarySurvival k m (S.filter (fun σ => auxiliarySatisfies σ C))) := by
  unfold auxiliarySurvival
  rw [Function.iterate_succ_apply']
  rfl

theorem local_iterates_block {r s k : ℕ} (j l : ℕ) (S : Finset (Assignment r))
    (T : Finset (Assignment s)) :
    ((embeddedAverage (Fin.castAdd s) k)^[j]
      ((embeddedAverage (Fin.natAdd r) k)^[l] alive)) (blockSet S T) =
      auxiliarySurvival k j S * auxiliarySurvival k l T := by
  induction j generalizing S T with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    change _ = alive S * auxiliarySurvival k l T
    induction l generalizing T with
    | zero => exact alive_blockSet S T
    | succ l ih =>
      rw [Function.iterate_succ_apply', auxiliarySurvival_succ, ← uniformMean_const_mul]
      unfold embeddedAverage finiteClauseAverage
      apply uniformMean_congr
      intro C
      rw [filter_blockSet_right]
      exact ih _
  | succ j ih =>
    rw [Function.iterate_succ_apply', auxiliarySurvival_succ, ← uniformMean_mul_const]
    unfold embeddedAverage finiteClauseAverage
    apply uniformMean_congr
    intro C
    rw [filter_blockSet_left]
    exact ih _ _

theorem auxiliary_interpolation {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (m : ℕ) :
    binomialMean ((r : ℝ) / (r + s)) m (fun j =>
      auxiliaryProbability r k j * auxiliaryProbability s k (m - j)) ≤
      auxiliaryProbability (r + s) k m := by
  have hp0 : 0 ≤ (r : ℝ) / (r + s) := by positivity
  have hp1 : (r : ℝ) / (r + s) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < r + s)).mpr
    exact le_add_of_nonneg_right (Nat.cast_nonneg s)
  have h := iterate_compare_of_commute (auxiliaryAverage (n := r + s) k)
    (mixedAverage ((r : ℝ) / (r + s)) (embeddedAverage (Fin.castAdd s) k)
      (embeddedAverage (Fin.natAdd r) k))
    (fun _ _ h => finiteClauseAverage_mono _ h) (mixedAverage_mono hp0 hp1
      (fun _ _ h => finiteClauseAverage_mono _ h) (fun _ _ h => finiteClauseAverage_mono _ h))
    (finiteClauseAverage_commute_mix _ _ _ _) (globalAverage_ge_local hr hs) m Finset.univ
  change _ ≤ auxiliaryProbability (r + s) k m at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold embeddedAverage
  rw [mixed_finiteAverage_iterate]
  apply binomialMean_congr
  intro j hj
  change _ = ((embeddedAverage (Fin.castAdd s) k)^[j]
      ((embeddedAverage (Fin.natAdd r) k)^[m - j] alive)) Finset.univ
  rw [← blockSet_univ r s, local_iterates_block]
  rfl

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Transfer
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem product_lower_two_deviations {κ x y a b : ℝ} (hκ : 0 ≤ κ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hax : x < 1 → κ ≤ a) (hby : y < 1 → κ ≤ b) :
    κ^2 * (1 - x - y) ≤ a * b := by
  by_cases hx1 : x < 1
  · by_cases hy1 : y < 1
    · have hprod := mul_le_mul (hax hx1) (hby hy1) hκ ha
      have hle : κ^2 * (1 - x - y) ≤ κ^2 :=
        by
          have hh : 1 - x - y ≤ 1 := by linarith
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (sq_nonneg κ)
      nlinarith
    · have hle : κ^2 * (1 - x - y) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (by linarith)
      exact hle.trans (mul_nonneg ha hb)
  · have hle : κ^2 * (1 - x - y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg κ) (by linarith)
    exact hle.trans (mul_nonneg ha hb)

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_CenterComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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
      apply auxiliaryProbability_center_lower_sat hk hr hrrep hrerr
      have hsq : ((j : ℝ) - m * p)^2 < (fluctuationWindow r k)^2 :=
        (div_lt_one (sq_pos_of_pos hwr)).mp hdev
      by_contra hgap
      have hdiff : fluctuationWindow r k < (j : ℝ) - m * p := by
        change (m : ℝ) * p + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k at hgapr
        linarith
      nlinarith
    · intro hdev
      apply auxiliaryProbability_center_lower_sat hk hs hsrep hserr
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

theorem densityWindow_pos {n k : ℕ} (hn : 0 < n) : 0 < densityWindow n k :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem fluctuationWindow_eq_mul {n k : ℕ} (hn : 0 < n) :
    fluctuationWindow n k = (n : ℝ) * densityWindow n k := by
  unfold fluctuationWindow densityWindow
  rw [sub_eq_add_neg, Real.rpow_add (by exact_mod_cast hn), Real.rpow_one]

theorem fluctuationWindow_one_le {n k : ℕ} (hk : 3 ≤ k) (hn : 0 < n) :
    1 ≤ fluctuationWindow n k := by
  apply Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have h := delta_lt_half hk
  linarith

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

theorem center_sum_comparison_of_bounds {r s k : ℕ} (hk : 3 ≤ k)
    (hr : k + 1 ≤ r) (hs : k + 1 ≤ s)
    (hrrep : 2 * repeatPairs k ≤ r) (hsrep : 2 * repeatPairs k ≤ s)
    (hrerr : concentrationError r k ≤ 1 / 2) (hserr : concentrationError s k ≤ 1 / 2)
    (hrsample : samplingError r k ≤ 1 / 4) (hssample : samplingError s k ≤ 1 / 4)
    (hNerr : concentrationError (r + s) k < (transferLower k)^2 / 2)
    (hlow : 2 * densityWindow (min r s) k ≤ min (center r k) (center s k)) :
    min (center r k) (center s k) - 4 * densityWindow (min r s) k ≤ center (r + s) k := by
  have hr0 : 0 < r := by omega
  have hs0 : 0 < s := by omega
  have hu0 : 0 < min r s := lt_min hr0 hs0
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hN' : (0 : ℝ) < (r : ℝ) + s := by positivity
  let c := min (center r k) (center s k) - 2 * densityWindow (min r s) k
  have hc0 : 0 ≤ c := sub_nonneg.mpr hlow
  have hcL : c ≤ capMultiplier k := by
    have hh := (min_le_left (center r k) (center s k)).trans (center_le_capMultiplier (by omega) hr0)
    dsimp [c]
    have hp := (densityWindow_pos (k := k) hu0).le
    linarith
  have hcr : c + 2 * densityWindow r k ≤ center r k := by
    have hd := densityWindow_antitone hk hu0 (min_le_left r s)
    have hh := min_le_left (center r k) (center s k)
    dsimp [c]
    linarith
  have hcs : c + 2 * densityWindow s k ≤ center s k := by
    have hd := densityWindow_antitone hk hu0 (min_le_right r s)
    have hh := min_le_right (center r k) (center s k)
    dsimp [c]
    linarith
  let m := ⌊c * ((r : ℝ) + s)⌋₊
  have hm : (m : ℝ) ≤ c * ((r : ℝ) + s) := Nat.floor_le (mul_nonneg hc0 hN'.le)
  have hmr : (m : ℝ) * ((r : ℝ) / (r + s)) ≤ c * r := by
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (r : ℝ) / (r + s) by positivity)
    have he : c * ((r : ℝ) + s) * ((r : ℝ) / (r + s)) = c * r := by field_simp
    rwa [he] at hh
  have hms : (m : ℝ) * ((s : ℝ) / (r + s)) ≤ c * s := by
    have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ (s : ℝ) / (r + s) by positivity)
    have he : c * ((r : ℝ) + s) * ((s : ℝ) / (r + s)) = c * s := by field_simp
    rwa [he] at hh
  have hprob := auxiliary_interpolation_center_lower hk hr hs hrrep hsrep hrerr hserr
    (hm.trans (mul_le_mul_of_nonneg_right hcL hN'.le))
    (show (m : ℝ) * ((r : ℝ) / (r + s)) + 2 * fluctuationWindow r k ≤ (r : ℝ) * center r k by
      rw [fluctuationWindow_eq_mul hr0]
      have hh := mul_le_mul_of_nonneg_left hcr hr'.le
      nlinarith)
    (show (m : ℝ) * ((s : ℝ) / (r + s)) + 2 * fluctuationWindow s k ≤ (s : ℝ) * center s k by
      rw [fluctuationWindow_eq_mul hs0]
      have hh := mul_le_mul_of_nonneg_left hcs hs'.le
      nlinarith)
  have hhalf : (transferLower k)^2 / 2 ≤ auxiliaryProbability (r + s) k m := by
    have hh := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - samplingError r k - samplingError s k by linarith)
      (sq_nonneg (transferLower k))
    nlinarith
  have hcN := center_lower_of_auxiliary_probability_sat hk (by omega : k + 1 ≤ r + s) hc0 hcL
    (show concentrationError (r + s) k < auxiliaryProbability (r + s) k ⌊c * ((r + s : ℕ) : ℝ)⌋₊ by
      simpa only [Nat.cast_add, ← show ⌊c * ((r : ℝ) + s)⌋₊ = m from rfl] using hNerr.trans_le hhalf)
  have hd := densityWindow_antitone hk hu0 (show min r s ≤ r + s by omega)
  dsimp [c] at hcN
  linarith

theorem neighborLower_pos (k : ℕ) : 0 < neighborLower k :=
  mul_pos (Real.exp_pos _) (transferLower_pos k)

@[simp] theorem auxiliaryProbability_zero (n k : ℕ) : auxiliaryProbability n k 0 = 1 := by
  simp only [auxiliaryProbability, auxiliarySurvival, Function.iterate_zero, id_eq, alive_univ]

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
  have hlocal := auxiliaryProbability_center_lower_sat hk hs hsrep hserr hgap
  have hpow := neighbor_pow_lower (k := k) hs0 hmL
  have hprod := mul_le_mul hpow hlocal (transferLower_pos k).le
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (s : ℝ) / (s + 1)) m)
  have hprob : neighborLower k ≤ auxiliaryProbability (s + 1) k m :=
    hprod.trans (neighbor_all_left hs0)
  have hcN := center_lower_of_auxiliary_probability_sat hk (by omega : k + 1 ≤ s + 1) hc0 hcL
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
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Convergence
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
A balanced-block geometric potential proves convergence from boundedness and
summable-min comparisons, including block counts that are not powers of two.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem balanceConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < balanceConstant β :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))

theorem balanced_power_potential {β a b q : ℝ} (hβ : 0 < β) (hb : 0 < b)
    (hq : 0 < q) (haq : q / 3 ≤ a) (hbq : b ≤ q / (3 / 2)) :
    a^(-β) ≤ balanceConstant β * (b^(-β) - q^(-β)) := by
  have hA := Real.rpow_le_rpow_of_nonpos (div_pos hq (by norm_num)) haq (neg_nonpos.mpr hβ.le)
  rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    div_inv_eq_mul] at hA
  have hB := Real.rpow_le_rpow_of_nonpos hb hbq (neg_nonpos.mpr hβ.le)
  rw [Real.div_rpow hq.le (by norm_num : (0 : ℝ) ≤ 3 / 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3 / 2), div_inv_eq_mul] at hB
  have hd : (3 / 2 : ℝ)^β - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hβ))
  have hf : balanceConstant β * ((3 / 2 : ℝ)^β - 1) = (3 : ℝ)^β := by
    exact div_mul_cancel₀ _ hd
  calc
    a^(-β) ≤ q^(-β) * (3 : ℝ)^β := hA
    _ = balanceConstant β * (q^(-β) * ((3 / 2 : ℝ)^β - 1)) := by rw [← hf]; ring
    _ ≤ balanceConstant β * (b^(-β) - q^(-β)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hB]) (balanceConstant_pos hβ).le

theorem balanced_blocks_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ q : ℕ, 1 ≤ q → ∀ r : ℕ, r ≤ q →
      u s - A * (s : ℝ)^(-β) -
        A * balanceConstant β * (s : ℝ)^(-β) * (1 - (q : ℝ)^(-β)) ≤ u (q * s + r) := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq r hr
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    have hpow : 0 ≤ (s : ℝ)^(-β) := (Real.rpow_pos_of_pos hs' _).le
    have hcoef : 0 ≤ A * balanceConstant β * (s : ℝ)^(-β) :=
      mul_nonneg (mul_nonneg hA (balanceConstant_pos hβ).le) hpow
    by_cases hq1 : q = 1
    · subst q
      have hr' : r = 0 ∨ r = 1 := by omega
      rcases hr' with hr0 | hr1
      · subst r
        simp only [Nat.cast_one, Real.one_rpow, sub_self, mul_zero, sub_zero, one_mul, add_zero]
        exact sub_le_self _ (mul_nonneg hA hpow)
      · subst r
        simpa only [Nat.cast_one, Real.one_rpow, sub_self, mul_zero, sub_zero, one_mul] using hnext
    · have hq2 : 2 ≤ q := by omega
      let a := q / 2
      let b := q - a
      let r₁ := min r a
      let r₂ := r - r₁
      have ha : 1 ≤ a := by dsimp [a]; omega
      have hb : 1 ≤ b := by dsimp [b, a]; omega
      have haq : a < q := by dsimp [a]; omega
      have hbq : b < q := by dsimp [b, a]; omega
      have hab : a ≤ b := by dsimp [a, b]; omega
      have habq : a + b = q := by dsimp [b, a]; omega
      have hqa : q ≤ 3 * a := by dsimp [a]; omega
      have hbq' : 3 * b ≤ 2 * q := by dsimp [b, a]; omega
      have hr₁ : r₁ ≤ a := min_le_right r a
      have hr₂ : r₂ ≤ b := by dsimp [r₂, r₁, b]; omega
      have hrr : r₁ + r₂ = r := by dsimp [r₂, r₁]; omega
      have hiA := ih a haq ha r₁ hr₁
      have hiB := ih b hbq hb r₂ hr₂
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hb' : (0 : ℝ) < b := by exact_mod_cast hb
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      have habpow : (b : ℝ)^(-β) ≤ (a : ℝ)^(-β) :=
        Real.rpow_le_rpow_of_nonpos ha' (by exact_mod_cast hab) (neg_nonpos.mpr hβ.le)
      have hchild : u s - A * (s : ℝ)^(-β) -
          A * balanceConstant β * (s : ℝ)^(-β) * (1 - (b : ℝ)^(-β)) ≤
          min (u (a * s + r₁)) (u (b * s + r₂)) := by
        apply le_min
        · have hh := mul_le_mul_of_nonneg_left habpow hcoef
          nlinarith
        · exact hiB
      have hsizeA : N ≤ a * s + r₁ := by nlinarith
      have hsizeB : N ≤ b * s + r₂ := by nlinarith
      have hsize : a * s ≤ min (a * s + r₁) (b * s + r₂) := by
        apply le_min <;> nlinarith
      have hminpos : (0 : ℝ) < (a : ℝ) * s := mul_pos ha' hs'
      have hminpow := Real.rpow_le_rpow_of_nonpos hminpos
        (show (a : ℝ) * s ≤ (min (a * s + r₁) (b * s + r₂) : ℝ) by exact_mod_cast hsize)
        (neg_nonpos.mpr hβ.le)
      rw [Real.mul_rpow ha'.le hs'.le] at hminpow
      have herr := mul_le_mul_of_nonneg_left hminpow hA
      have hpotential := balanced_power_potential hβ hb' hq'
        (show (q : ℝ) / 3 ≤ a by
          have hh : (q : ℝ) ≤ 3 * a := by exact_mod_cast hqa
          linarith)
        (show (b : ℝ) ≤ q / (3 / 2) by
          have hh : 3 * (b : ℝ) ≤ 2 * q := by exact_mod_cast hbq'
          linarith)
      have hpot := mul_le_mul_of_nonneg_left hpotential (mul_nonneg hA hpow)
      have hc := hadd (a * s + r₁) hsizeA (b * s + r₂) hsizeB
      have he : a * s + r₁ + (b * s + r₂) = q * s + r := by
        calc
          _ = (a + b) * s + (r₁ + r₂) := by ring
          _ = _ := by rw [habq, hrr]
      rw [he] at hc
      simp only [Nat.cast_add, Nat.cast_mul] at hc
      nlinarith

theorem balanced_tail_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ n ≥ s * s,
      u s - A * (1 + balanceConstant β) * (s : ℝ)^(-β) ≤ u n := by
  intro n hn
  have hq : s ≤ n / s := (Nat.le_div_iff_mul_le hs).mpr hn
  have hr : n % s ≤ n / s := (Nat.mod_lt n hs).le.trans hq
  have hb := balanced_blocks_bound u hA hβ hsN hs hadd hnext (n / s) (by omega) (n % s) hr
  rw [Nat.mul_comm (n / s) s, Nat.div_add_mod] at hb
  have hcoef : 0 ≤ A * balanceConstant β * (s : ℝ)^(-β) * ((n / s : ℕ) : ℝ)^(-β) := by
    have hB := (balanceConstant_pos hβ).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hA hB) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  nlinarith

theorem summable_min_convergence (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u)
    (hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (hcompare : ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N, min (u r) (u s) - A * (min r s : ℝ)^(-β) ≤ u (r + s)) ∧
      (∀ s ≥ N, u s - A * (s : ℝ)^(-β) ≤ u (s + 1))) :
    Filter.Tendsto u Filter.atTop (nhds (Filter.limsup u Filter.atTop)) := by
  obtain ⟨N, hadd, hnext⟩ := hcompare
  let α := Filter.limsup u Filter.atTop
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let ε := (α - a) / 3
    have hε : 0 < ε := by dsimp [ε, α]; linarith
    have ht := (tendsto_rpow_neg_atTop hβ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hcost : Filter.Tendsto (fun s : ℕ => A * (1 + balanceConstant β) * (s : ℝ)^(-β))
        Filter.atTop (nhds 0) := by
      simpa only [Function.comp_apply, mul_zero] using ht.const_mul (A * (1 + balanceConstant β))
    have hsmall := hcost.eventually_lt_const hε
    have hhigh : ∃ᶠ s : ℕ in Filter.atTop, α - ε < u s :=
      Filter.frequently_lt_of_lt_limsup hLower.isCoboundedUnder_le (by change α - ε < α; linarith)
    have hgood : ∀ᶠ s : ℕ in Filter.atTop,
        N ≤ s ∧ 0 < s ∧ A * (1 + balanceConstant β) * (s : ℝ)^(-β) < ε := by
      filter_upwards [Filter.eventually_ge_atTop (max N 1), hsmall] with s hs he
      exact ⟨by omega, by omega, he⟩
    obtain ⟨s, hsHigh, hsN, hs, hsSmall⟩ := (hhigh.and_eventually hgood).exists
    have htail := balanced_tail_bound u hA hβ hsN hs hadd (hnext s hsN)
    filter_upwards [Filter.eventually_ge_atTop (s * s)] with n hn
    have hh := htail n hn
    dsimp [ε] at hsHigh hsSmall
    linarith
  · intro a ha
    exact Filter.eventually_lt_of_limsup_lt ha hUpper

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Main
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

theorem center_tendsto (k : ℕ) (hk : 3 ≤ k) :
    Filter.Tendsto (fun n : ℕ => center n k) Filter.atTop (nhds (limitingCenter k)) := by
  have hb := center_bounds_eventually k hk
  have hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun n : ℕ => center n k) :=
    Filter.isBoundedUnder_of_eventually_le (hb.mono (fun _ h => h.2))
  have hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop (fun n : ℕ => center n k) :=
    Filter.isBoundedUnder_of_eventually_ge (hb.mono (fun _ h => h.1))
  apply summable_min_convergence (fun n => center n k) (by norm_num : (0 : ℝ) ≤ 4)
    (delta_pos hk) hUpper hLower
  obtain ⟨N, hadd, hnext⟩ := center_comparisons k hk
  refine ⟨N, ?_, ?_⟩
  · intro r hr s hs
    simpa only [densityWindow, Nat.cast_min] using hadd r hr s hs
  · intro s hs
    exact hnext s hs

theorem floor_density_le_cap {n k : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k) :
    ⌊c * (n : ℝ)⌋₊ ≤ mainCap n k := by
  have h := (Nat.floor_le (mul_nonneg hc0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))).trans
    (mul_le_mul_of_nonneg_right hcL (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  exact_mod_cast (show (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ (mainCap n k : ℝ) by
    simpa only [mainCap, Nat.cast_mul] using h)

theorem supercritical_limit_below_cap (k : ℕ) (hk : 3 ≤ k) (c : ℝ)
    (hc : limitingCenter k < c) (hcL : c ≤ capMultiplier k) :
    Filter.Tendsto (fun n : ℕ => properSATProbability n k ⌊c * (n : ℝ)⌋₊)
      Filter.atTop (nhds 0) := by
  have hc0 : 0 ≤ c := ((limitingCenter_pos_sat k hk).trans hc).le
  have hd : Filter.Tendsto (fun n : ℕ => 2 * densityWindow n k) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using (densityWindow_tendsto k hk).const_mul (2 : ℝ)
  have hcenter : Filter.Tendsto (fun n : ℕ => center n k + 2 * densityWindow n k)
      Filter.atTop (nhds (limitingCenter k)) := by
    simpa only [add_zero] using (center_tendsto k hk).add hd
  have hmargin := hcenter.eventually_lt_const hc
  have hupper : ∀ᶠ n : ℕ in Filter.atTop,
      properSATProbability n k ⌊c * (n : ℝ)⌋₊ ≤ concentrationError n k := by
    filter_upwards [hmargin, Filter.eventually_ge_atTop (k + 1)] with n hmargin hn
    apply properSATProbability_center_upper_sat hk hn (floor_density_le_cap hc0 hcL)
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
  have hd : limitingCenter k < d := lt_min hc (limitingCenter_lt_cap_sat k hk)
  have hdL : d ≤ capMultiplier k := min_le_right _ _
  have ht := supercritical_limit_below_cap k hk d hd hdL
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => properSATProbability_nonneg n k _) _ ht
  filter_upwards [Filter.eventually_ge_atTop k] with n hn
  apply properSATProbability_antitone hn
  exact Nat.floor_mono (mul_le_mul_of_nonneg_right (min_le_left c (capMultiplier k : ℝ)) (Nat.cast_nonneg n))

end


end FixedClauseThreshold

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology NNReal

theorem main_oai : MainStatement := by
  obtain ⟨q,c,hq,hc,he⟩ := threshold_program_sat
  exact ⟨limitingCenter 3,q,c,limitingCenter_pos_sat 3 (by decide),
    subcritical_limit_sat 3 (by decide),supercritical_limit 3 (by decide),
    Computable.encode_iff.mpr hq,hc,he⟩

end FixedClauseThreshold.Computability

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.main_oai := @OAI.FixedClauseThreshold.Computability.main_oai
