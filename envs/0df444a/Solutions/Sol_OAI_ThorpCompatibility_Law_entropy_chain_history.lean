-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.entropy_chain_history
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:39:36.646154+00:00
-- url     : https://prove2.me/submissions/8caad6ed-fd56-424d-a6c8-20b3696ee19f

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/EntropyChain.lean:L87-L115
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.entropy_chain_history. The node keeps its source
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

omit [Fintype α] [Fintype β] in
lemma history_eq_iff {n : ℕ} (X : Fin n → α → β) (t : ℕ) (a b : α) :
    history X t a = history X t b ↔ ∀ i : Fin n, (i : ℕ) < t → X i a = X i b := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa [history, hi] using he
  · intro h
    funext i
    by_cases hi : (i : ℕ) < t
    · simp [history, hi, h i hi]
    · simp [history, hi]

omit [Fintype α] [Fintype β] [Fintype γ] in
lemma history_step_fibers {n : ℕ} (X : Fin n → α → β) (Y : α → γ)
    (i : Fin n) (a b : α) :
    (X i a, (Y a, history X i a)) = (X i b, (Y b, history X i b)) ↔
      (Y a, history X (i + 1) a) = (Y b, history X (i + 1) b) := by
  simp only [Prod.mk.injEq, history_eq_iff]
  constructor
  · rintro ⟨hi, hY, hprev⟩
    refine ⟨hY, fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
    · exact hprev j hlt
    · have he : j = i := Fin.ext heq
      simpa [he] using hi
  · rintro ⟨hY, hprev⟩
    exact ⟨hprev i (Nat.lt_succ_self _), hY,
      fun j hj => hprev j (Nat.lt_succ_of_lt hj)⟩

lemma sum_fin_telescope (n : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin n, (f (i + 1) - f i)) = f n - f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

lemma entropy_chain_history {n : ℕ} (P : Law α) (X : Fin n → α → β) (Y : α → γ) :
    (∑ i : Fin n, P.condEntropy (X i) (fun a => (Y a, history X i a))) =
      P.condEntropy (fun a i => X i a) Y := by
  let F : ℕ → ℝ := fun t => (P.map (fun a => (Y a, history X t a))).entropy
  have hs (i : Fin n) :
      P.condEntropy (X i) (fun a => (Y a, history X i a)) = F (i + 1) - F i := by
    unfold condEntropy F
    rw [P.entropy_eq_of_fibers _ _ (history_step_fibers X Y i)]
  simp_rw [hs]
  rw [sum_fin_telescope]
  have hfull : F n = (P.map (fun a => ((fun i => X i a), Y a))).entropy := by
    apply P.entropy_eq_of_fibers
    intro a b
    simp only [Prod.mk.injEq]
    rw [history_eq_iff]
    simp only [funext_iff]
    constructor
    · rintro ⟨hY, hX⟩
      exact ⟨fun i => hX i i.isLt, hY⟩
    · rintro ⟨hX, hY⟩
      exact ⟨hY, fun i _ => hX i⟩
  have hzero : F 0 = (P.map Y).entropy := by
    apply P.entropy_eq_of_fibers
    intro a b
    simp only [Prod.mk.injEq]
    rw [history_eq_iff]
    simp
  rw [hfull, hzero]
  rfl

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

theorem solution {n : ℕ} (P : Law α) (X : Fin n → α → β) (Y : α → γ) :
    (∑ i : Fin n, P.condEntropy (X i) (fun a => (Y a, history X i a))) =
      P.condEntropy (fun a i => X i a) Y := by
  first
    | exact OAI.ThorpCompatibility.Law.entropy_chain_history P X Y
    | exact OAI.ThorpCompatibility.Law.entropy_chain_history
    | (apply OAI.ThorpCompatibility.Law.entropy_chain_history <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.entropy_chain_history <;> assumption)
