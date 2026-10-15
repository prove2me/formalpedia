-- Prove2me | solution 1 for OAI.FixedClauseThreshold.uniformProbability_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:34:26.940059+00:00
-- url     : https://prove2.me/submissions/faa104d6-65dc-4ddb-afa0-082ba19e5b35

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/CenterBounds.lean:L22-L38
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.uniformProbability_exists_le. The node keeps its source
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

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    uniformMean (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm, Finset.sum_div]

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

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.uniformProbability_exists_le := @_root_.OAI.FixedClauseThreshold.uniformProbability_exists_le
