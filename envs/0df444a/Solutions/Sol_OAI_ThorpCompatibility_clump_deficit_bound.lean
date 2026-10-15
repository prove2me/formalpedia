-- Prove2me | solution 1 for OAI.ThorpCompatibility.clump_deficit_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:04:49.303823+00:00
-- url     : https://prove2.me/submissions/8b93fa46-8e11-42e9-af62-d5c96407ba24

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/GridDeficits.lean:L50-L70
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.clump_deficit_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits
import Theorems.Thm_OAI_ThorpCompatibility_Law_gibbs_le

-- ---- from OAI.Probability.ThorpCompatibility.FiniteLaw ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).mean g = P.mean (g ∘ f) := by
  classical
  simp only [mean, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma entropy_moment_bound [Nonempty α] (P : Law α) (f : α → ℝ) :
    P.mean f ≤ P.uniformDeficit +
      Real.log ((∑ x, Real.exp (f x)) / Fintype.card α) := by
  have hZ : 0 < ∑ x, Real.exp (f x) := Finset.sum_pos
    (fun x _ => Real.exp_pos _) Finset.univ_nonempty
  have h := P.gibbs_le (fun x => Real.exp (f x)) (fun x => (Real.exp_pos _).le)
    hZ (fun x hx => False.elim ((Real.exp_ne_zero _) hx))
  simp only [Real.log_exp] at h
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Real.log_div hZ.ne' hc]
  unfold uniformDeficit
  linarith

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mean_mul_const (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.mean (fun a => f a * c) = P.mean f * c := by
  simp [mean, ← mul_assoc, Finset.sum_mul]

lemma mean_const_mul (P : Law α) (c : ℝ) (f : α → ℝ) :
    P.mean (fun a => c * f a) = c * P.mean f := by
  simpa [mul_comm] using P.mean_mul_const f c

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.GridDeficits ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma clump_deficit_bound {A D : ℕ} (Q : Law (Grid A D)) (m : ℝ)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2) :
    Real.log m * Q.mean (fun a => (clumpCount (m^(1/100:ℝ)) a.1 : ℝ)) ≤
      400 * jointRowDeficit Q + 400 := by
  let f : Rows A D → ℝ := fun r => (1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r
  have h := (Q.map Prod.fst).entropy_moment_bound f
  have hpos : 0 < uniformMean (fun r => Real.exp (f r)) := by
    unfold uniformMean
    apply div_pos
    · exact Finset.sum_pos (fun r _ => Real.exp_pos _) Finset.univ_nonempty
    · exact_mod_cast Fintype.card_pos
  have hlog : Real.log (uniformMean (fun r => Real.exp (f r))) ≤ 1 := by
    have h₂ := Real.log_le_log hpos hmgf
    have h₃ := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  change _ ≤ jointRowDeficit Q + Real.log (uniformMean (fun r => Real.exp (f r))) at h
  rw [Law.mean_map] at h
  change Q.mean (fun a => (1/400 * Real.log m) * (clumpCount (m^(1/100:ℝ)) a.1 : ℝ)) ≤ _ at h
  rw [Law.mean_const_mul] at h
  nlinarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} (Q : Law (Grid A D)) (m : ℝ)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2) :
    Real.log m * Q.mean (fun a => (clumpCount (m^(1/100:ℝ)) a.1 : ℝ)) ≤
      400 * jointRowDeficit Q + 400 := by
  first
    | exact OAI.ThorpCompatibility.clump_deficit_bound Q m hmgf
    | exact OAI.ThorpCompatibility.clump_deficit_bound
    | (apply OAI.ThorpCompatibility.clump_deficit_bound <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.clump_deficit_bound <;> assumption)
