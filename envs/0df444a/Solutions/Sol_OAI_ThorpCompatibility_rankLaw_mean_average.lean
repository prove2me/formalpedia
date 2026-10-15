-- Prove2me | solution 1 for OAI.ThorpCompatibility.rankLaw_mean_average
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:35:23.121999+00:00
-- url     : https://prove2.me/submissions/b0402fc6-7ee2-4a26-844b-e4fbca619bc1

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/RankAverages.lean:L65-L80
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.rankLaw_mean_average. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_Law_mean_predict
import Theorems.Thm_OAI_ThorpCompatibility_uniform_rank_prob

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

lemma map_id (P : Law α) : P.map id = P := by
  classical
  ext a
  simp [map]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Prediction ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma prob_eq_map_mass (P : Law α) (Y : α → γ) (y : γ) :
    P.prob (fun a => Y a = y) = (P.map Y).mass y := by rfl

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.RankAverages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

end Law
open Finset

lemma rankLaw_mean_average {D : ℕ} (k : Fin D) (g : Equiv.Perm (Fin D) → ℝ) :
    (∑ t, (rankLaw k t).mean g) / (D : ℝ) =
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean g := by
  let P : Law (Equiv.Perm (Fin D)) := Law.uniform
  have h := P.mean_predict id (fun e => e k) (fun _ e => g e)
  have he : P.mean (fun e => (P.predict id (fun e => e k) (e k)).mean g) =
      (P.map (fun e => e k)).mean (fun t => (rankLaw k t).mean g) := by
    rw [P.mean_map]
    simp only [Law.predict, Law.map_id, rankLaw, P]
    rfl
  rw [he] at h
  have hm (t : Fin D) : (P.map (fun e => e k)).mass t = 1 / (D : ℝ) := by
    rw [← P.prob_eq_map_mass]
    exact uniform_rank_prob k t
  simpa only [Law.mean, hm, id_eq, one_div, ← Finset.mul_sum, div_eq_mul_inv,
    mul_comm, mul_one, P] using h

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {D : ℕ} (k : Fin D) (g : Equiv.Perm (Fin D) → ℝ) :
    (∑ t, (rankLaw k t).mean g) / (D : ℝ) =
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean g := by
  first
    | exact OAI.ThorpCompatibility.rankLaw_mean_average k g
    | exact OAI.ThorpCompatibility.rankLaw_mean_average
    | (apply OAI.ThorpCompatibility.rankLaw_mean_average <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.rankLaw_mean_average <;> assumption)
