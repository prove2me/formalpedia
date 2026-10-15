-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.map_mass_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:22:42.221146+00:00
-- url     : https://prove2.me/submissions/80138ef7-7160-4205-b47d-35be18cf7a9c

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ConditionalEntropy.lean:L12-L24
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.map_mass_pos_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy

-- ---- from OAI.Probability.ThorpCompatibility.ConditionalEntropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma map_mass_pos_iff (P : Law α) (f : α → β) (b : β) :
    0 < (P.map f).mass b ↔ ∃ a, f a = b ∧ 0 < P.mass a := by
  classical
  unfold map
  rw [Finset.sum_pos_iff_of_nonneg (fun a _ => by split_ifs <;> simp_all [P.nonneg])]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha⟩
    split_ifs at ha with hab
    · exact ⟨a, hab, ha⟩
    · exact False.elim (lt_irrefl _ ha)
  · rintro ⟨a, hab, ha⟩
    exact ⟨a, by simpa [hab] using ha⟩

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem solution (P : Law α) (f : α → β) (b : β) :
    0 < (P.map f).mass b ↔ ∃ a, f a = b ∧ 0 < P.mass a := by
  first
    | exact OAI.ThorpCompatibility.Law.map_mass_pos_iff P f b
    | exact OAI.ThorpCompatibility.Law.map_mass_pos_iff
    | (apply OAI.ThorpCompatibility.Law.map_mass_pos_iff <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.map_mass_pos_iff <;> assumption)
