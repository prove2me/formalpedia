-- Prove2me | solution 1 for OAI.ThorpCompatibility.rowDeficit_le_joint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:02:37.711977+00:00
-- url     : https://prove2.me/submissions/486bca85-be86-47de-9c47-0964707c7038

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/GridDeficits.lean:L36-L48
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.rowDeficit_le_joint. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_le_prediction
import Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain

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

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

lemma uniformDeficit_eq (P : Law α) :
    P.uniformDeficit = Real.log (Fintype.card α) - P.entropy := by
  simp [uniformDeficit, entropy, mean]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.EntropyChain ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma condEntropy_le_entropy (P : Law α) (X : α → β) (Y : α → γ) :
    P.condEntropy X Y ≤ (P.map X).entropy := by
  have h := P.condEntropy_le_prediction X Y (fun _ => P.map X)
    (fun a ha => P.map_mass_pos X ha)
  simpa [entropy, P.mean_map, Function.comp_def] using h

lemma entropy_tuple_le {n : ℕ} (P : Law α) (X : Fin n → α → β) :
    (P.map (fun a i => X i a)).entropy ≤ ∑ i, (P.map (X i)).entropy := by
  rw [← P.entropy_chain X]
  exact Finset.sum_le_sum fun i _ => P.condEntropy_le_entropy (X i) (history X i)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.GridDeficits ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma rowDeficit_le_joint {A D : ℕ} (Q : Law (Grid A D)) :
    rowDeficit Q ≤ jointRowDeficit Q := by
  have h := Q.entropy_tuple_le (fun i : Fin A => fun a => a.1 i)
  change (Q.map Prod.fst).entropy ≤ _ at h
  unfold rowDeficit jointRowDeficit
  simp only [Law.uniformDeficit_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : Real.log (Fintype.card (Rows A D) : ℝ) =
      A * Real.log (Fintype.card (Equiv.Perm (Fin D)) : ℝ) := by
    change Real.log (Fintype.card (Fin A → Equiv.Perm (Fin D)) : ℝ) = _
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  rw [hc]
  linarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} (Q : Law (Grid A D)) :
    rowDeficit Q ≤ jointRowDeficit Q := by
  first
    | exact OAI.ThorpCompatibility.rowDeficit_le_joint Q
    | exact OAI.ThorpCompatibility.rowDeficit_le_joint
    | (apply OAI.ThorpCompatibility.rowDeficit_le_joint <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.rowDeficit_le_joint <;> assumption)
