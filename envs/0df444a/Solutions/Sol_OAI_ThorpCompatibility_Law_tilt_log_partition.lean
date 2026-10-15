-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.tilt_log_partition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:09:16.422985+00:00
-- url     : https://prove2.me/submissions/a2cab90c-fa89-4294-b916-caabef70e983

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/WeightedGibbs.lean:L69-L87
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.tilt_log_partition. The node keeps its source
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

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, P.total]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

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

lemma tilt_log_partition [Nonempty α] (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) :
    (Law.tilt a ha hZ).mean (fun x => Real.log (a x)) -
      (Law.tilt a ha hZ).uniformDeficit = Real.log (uniformMean a) := by
  let P := Law.tilt a ha hZ
  have he : P.mean (fun x => Real.log (P.mass x)) =
      P.mean (fun x => Real.log (a x)) - Real.log (∑ x, a x) := by
    rw [← P.mean_const (Real.log (∑ x, a x)), ← P.mean_sub]
    apply P.mean_congr_support
    intro x hx
    have hax : a x ≠ 0 := by intro hz; simp [P, Law.tilt, hz] at hx
    exact Real.log_div hax hZ.ne'
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change P.mean _ - P.uniformDeficit = _
  change P.mean _ - (Real.log (Fintype.card α) + P.mean (fun x => Real.log (P.mass x))) = _
  rw [he]
  unfold uniformMean
  rw [Real.log_div hZ.ne' hc]
  ring

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem solution [Nonempty α] (a : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hZ : 0 < ∑ x, a x) :
    (Law.tilt a ha hZ).mean (fun x => Real.log (a x)) -
      (Law.tilt a ha hZ).uniformDeficit = Real.log (uniformMean a) := by
  first
    | exact OAI.ThorpCompatibility.Law.tilt_log_partition a ha hZ
    | exact OAI.ThorpCompatibility.Law.tilt_log_partition
    | (apply OAI.ThorpCompatibility.Law.tilt_log_partition <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.tilt_log_partition <;> assumption)
