-- Prove2me | solution 1 for OAI.ThorpCompatibility.gridAllowed_iff_rank
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:42:45.077002+00:00
-- url     : https://prove2.me/submissions/73912b3b-f953-48a5-a463-746e9287a2d5

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/GridExposure.lean:L51-L70
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.gridAllowed_iff_rank. The node keeps its source
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

-- ---- from OAI.Probability.ThorpCompatibility.GridExposure ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma gridAllowed_iff_rank {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (w : Fin A) :
    gridAllowed k i (gridPast e k i a) w ↔ e k ≤ e (columnFor a ha ((a.1 i).symm k) w) := by
  let j := (a.1 i).symm k
  let h := (outputEquiv a ha j).symm w
  have hout : a.2 (a.1 h j) h = w := (outputEquiv a ha j).apply_symm_apply w
  change gridAllowed k i (gridPast e k i a) w ↔ e k ≤ e (a.1 h j)
  constructor
  · intro hall
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hx := hall h (a.2 (a.1 h j)) (by simp [gridPast, priorCols, j, hlt])
    exact hx hout
  · intro hle l σ hσ heq
    dsimp [gridPast, priorCols] at hσ
    split_ifs at hσ with hlt
    · have hσ' : a.2 (a.1 l j) = σ := Option.some.inj hσ
      have hlh : l = h := ha j (by change a.2 (a.1 l j) l = a.2 (a.1 h j) h; rw [hσ', heq, hout])
      subst l
      exact (not_lt_of_ge hle) hlt

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (w : Fin A) :
    gridAllowed k i (gridPast e k i a) w ↔ e k ≤ e (columnFor a ha ((a.1 i).symm k) w) := by
  first
    | exact OAI.ThorpCompatibility.gridAllowed_iff_rank a ha e k i w
    | exact OAI.ThorpCompatibility.gridAllowed_iff_rank
    | (apply OAI.ThorpCompatibility.gridAllowed_iff_rank <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.gridAllowed_iff_rank <;> assumption)
