-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.weighted_gibbs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:07:18.294635+00:00
-- url     : https://prove2.me/submissions/c1d3c5cf-f012-4ec9-ac8b-a120e3489119

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/WeightedGibbs.lean:L38-L67
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.weighted_gibbs_le. The node keeps its source
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

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.WeightedGibbs ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility

end ThorpCompatibility

namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma exists_mass_pos (P : Law α) : ∃ x, 0 < P.mass x := by
  by_contra h
  push Not at h
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => h x)
  simp only [P.total, Finset.sum_const_zero] at hh
  linarith

lemma uniformMean_rpow_pos [Nonempty α] (P : Law α) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) (p : ℝ) :
    0 < uniformMean (fun x => (w x)^p) := by
  obtain ⟨x,hx⟩ := P.exists_mass_pos
  have hwx : 0 < w x := lt_of_le_of_ne (hw x) (by
    intro he
    exact hx.ne' (hs x he.symm))
  unfold uniformMean
  apply div_pos
  · exact lt_of_lt_of_le (Real.rpow_pos_of_pos hwx p)
      (Finset.single_le_sum (fun y _ => Real.rpow_nonneg (hw y) p) (Finset.mem_univ x))
  · exact_mod_cast Fintype.card_pos

lemma weighted_gibbs_le [Nonempty α] (P : Law α) {θ : ℝ} (hθ : 0 < θ)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (w x)) - θ*P.uniformDeficit ≤
      Real.log (marginalFactor θ w) := by
  have hZ : 0 < ∑ x, (w x)^(1/θ) := by
    have h := P.uniformMean_rpow_pos w hw hs (1/θ)
    exact (div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)).mp h
  have h := P.gibbs_le (fun x => (w x)^(1/θ))
    (fun x => Real.rpow_nonneg (hw x) _) hZ (by
      intro x hz
      by_cases hx : w x = 0
      · exact hs x hx
      · exact False.elim ((Real.rpow_pos_of_pos (lt_of_le_of_ne (hw x) (Ne.symm hx)) _).ne' hz))
  have he : P.mean (fun x => Real.log ((w x)^(1/θ))) =
      (1/θ)*P.mean (fun x => Real.log (w x)) := by
    rw [← P.mean_const_mul]
    apply P.mean_congr_support
    intro x hx
    apply Real.log_rpow
    exact lt_of_le_of_ne (hw x) (by intro he; exact hx.ne' (hs x he.symm))
  rw [he] at h
  have hmean := P.uniformMean_rpow_pos w hw hs (1/θ)
  simp only [marginalFactor, Real.rpow_eq_pow]
  rw [Real.log_rpow hmean, uniformMean,
    Real.log_div hZ.ne' (by exact_mod_cast Fintype.card_ne_zero)]
  have hh := mul_le_mul_of_nonneg_left h hθ.le
  have ht : θ*(1/θ) = 1 := by field_simp
  rw [mul_sub, ← mul_assoc, ht, one_mul] at hh
  unfold uniformDeficit
  nlinarith

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem solution [Nonempty α] (P : Law α) {θ : ℝ} (hθ : 0 < θ)
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) :
    P.mean (fun x => Real.log (w x)) - θ*P.uniformDeficit ≤
      Real.log (marginalFactor θ w) := by
  first
    | exact OAI.ThorpCompatibility.Law.weighted_gibbs_le P hθ w hw hs
    | exact OAI.ThorpCompatibility.Law.weighted_gibbs_le
    | (apply OAI.ThorpCompatibility.Law.weighted_gibbs_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.weighted_gibbs_le <;> assumption)
