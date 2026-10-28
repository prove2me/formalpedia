-- Prove2me | solution 1 for OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:53:38.425178+00:00
-- url     : https://prove2.me/submissions/5e6e172d-dd61-4ead-a4b0-454145475e10

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_OAIQ067A002
import Theorems.Thm_OAI_FixedClauseThreshold_properSATProbability_center_lower_sat

section
-- module Solutions.OAIQ067_SAT.RandomSAT_Clauses
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.FixedClauseThreshold.Computability.decidableClauseSatisfaction _root_.OAI.FixedClauseThreshold.Computability.decidableFormulaSatisfaction _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem uniformMean_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

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

@[simp] theorem survival_empty {n k m : ℕ} : survival k m (∅ : Finset (Assignment n)) = 0 := by
  rw [survival_eq_mean]
  have h (F : Formula n k m) : restrictSolutions ∅ F = ∅ := by simp [restrictSolutions]
  simp only [h, alive_empty, uniformMean_zero]

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
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
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

theorem clauseAverage_alive {n k : ℕ} (hkn : k ≤ n) (S : Finset (Assignment n)) :
    clauseAverage k alive S = alive S * (1 - killFraction (forcedVariables S).card n k) := by
  by_cases hS : S.Nonempty
  · have h := singleUNSAT_eq hkn S
    have he : (uniformProbability (fun C : ProperClause n k => KillsSolutions S C)) =
        killingProbability k S := by
      apply uniformProbability_congr
      exact fun _ => (and_iff_right hS).symm
    rw [he, killingProbability_of_nonempty S hS] at h
    change killFraction _ _ _ = 1 - clauseAverage k alive S at h
    simp only [alive, ite_eq_left hS, one_mul]
    linarith
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [clauseAverage, addClause, alive_empty, uniformMean_zero]

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

theorem auxiliaryProbability_center_lower_sat_oai {n k m : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
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
  have hprob := properSATProbability_center_lower_sat hk hn hm hgap
  have hhalf : (1 / 2 : ℝ) ≤ properSATProbability n k m := by linarith
  have hmul := mul_le_mul (properFraction_pow_lower hn0 (by omega) hnrep hm) hhalf
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (properFraction_nonneg n k |> fun h => pow_nonneg h m)
  apply le_trans _ (proper_scaled_le_auxiliaryProbability hn0 (by omega) m)
  simpa only [transferLower, div_eq_mul_inv, one_mul] using hmul

end


end FixedClauseThreshold

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat_oai := @OAI.FixedClauseThreshold.auxiliaryProbability_center_lower_sat_oai
