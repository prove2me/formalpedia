-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.entropy_chain
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:41:03.209087+00:00
-- url     : https://prove2.me/submissions/56599774-f0d8-45cb-b810-d00735707d82

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/EntropyChain.lean:L117-L131
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.entropy_chain. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain_history

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

lemma map_mass_mean (P : Law α) (f : α → β) (b : β) :
    (P.map f).mass b = P.mean (fun a => if f a = b then 1 else 0) := by
  classical
  simp [map, mean, mul_ite]

lemma map_map (P : Law α) (f : α → β) (g : β → γ) :
    (P.map f).map g = P.map (g ∘ f) := by
  classical
  ext c
  rw [map_mass_mean, P.mean_map, map_mass_mean]
  rfl

lemma entropy_map_injective (P : Law α) (f : α → β) (hf : Function.Injective f) :
    (P.map f).entropy = P.entropy := by
  classical
  have hm (a : α) : (P.map f).mass (f a) = P.mass a := by
    simp [map, hf.eq_iff]
  unfold entropy
  rw [P.mean_map]
  simp only [Function.comp_def, hm]

lemma entropy_func_pair (P : Law α) (X : α → β) (f : β → γ) :
    (P.map (fun a => (X a, f (X a)))).entropy = (P.map X).entropy := by
  have hi : Function.Injective (fun b => (b, f b)) := fun _ _ h => congrArg Prod.fst h
  simpa [map_map, Function.comp_def] using (P.map X).entropy_map_injective _ hi

lemma condEntropy_const (P : Law α) (X : α → β) (c : γ) :
    P.condEntropy X (fun _ => c) = (P.map X).entropy := by
  have hz : (P.map (fun _ => c)).entropy = 0 := by
    classical
    unfold entropy
    rw [P.mean_map]
    have hc : (P.map (fun _ => c)).mass c = 1 := by simp [map, P.total]
    simp [hc, mean]
  rw [condEntropy, hz, sub_zero]
  exact P.entropy_func_pair X (fun _ => c)

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

lemma entropy_eq_of_fibers (P : Law α) (X : α → β) (Y : α → γ)
    (hf : ∀ a b, X a = X b ↔ Y a = Y b) : (P.map X).entropy = (P.map Y).entropy := by
  have hm (a : α) : (P.map X).mass (X a) = (P.map Y).mass (Y a) := by
    simp only [map]
    apply Finset.sum_congr rfl
    intro b _
    rw [hf b a]
  unfold entropy
  rw [P.mean_map, P.mean_map]
  simp only [Function.comp_def, hm]

lemma entropy_chain {n : ℕ} (P : Law α) (X : Fin n → α → β) :
    (∑ i : Fin n, P.condEntropy (X i) (history X i)) =
      (P.map (fun a i => X i a)).entropy := by
  have h := P.entropy_chain_history X (fun _ => ())
  have he (i : Fin n) :
      P.condEntropy (X i) (fun a => ((), history X i a)) =
        P.condEntropy (X i) (history X i) := by
    unfold condEntropy
    have h₁ := P.entropy_eq_of_fibers (fun a => (X i a, ((), history X i a)))
      (fun a => (X i a, history X i a)) (by intro a b; simp)
    have h₂ := P.entropy_eq_of_fibers (fun a => ((), history X i a))
      (history X i) (by intro a b; simp)
    rw [h₁, h₂]
  simp_rw [he] at h
  simpa [P.condEntropy_const] using h

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem solution {n : ℕ} (P : Law α) (X : Fin n → α → β) :
    (∑ i : Fin n, P.condEntropy (X i) (history X i)) =
      (P.map (fun a i => X i a)).entropy := by
  first
    | exact OAI.ThorpCompatibility.Law.entropy_chain P X
    | exact OAI.ThorpCompatibility.Law.entropy_chain
    | (apply OAI.ThorpCompatibility.Law.entropy_chain <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.entropy_chain <;> assumption)
