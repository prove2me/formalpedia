-- Prove2me | solution 1 for OAI.FixedClauseThreshold.embeddedAverage_alive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:42:08.570424+00:00
-- url     : https://prove2.me/submissions/44f1c390-18f6-4d78-b792-32c926b69943

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Interpolation.lean:L207-L231
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.embeddedAverage_alive. The node keeps its source
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

theorem uniformProbability_eq_mean {α : Type*} [Fintype α] (p : α → Prop) :
    uniformProbability p = uniformMean (fun a => if p a then 1 else 0) := by
  classical
  unfold uniformProbability uniformMean
  congr 1
  simp [Fintype.card_subtype]

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

-- ---- from OAI.Probability.RandomSAT.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.embeddedAverage_alive := @_root_.OAI.FixedClauseThreshold.embeddedAverage_alive
