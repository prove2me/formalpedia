-- Prove2me | solution 1 for OAI.ThorpCompatibility.grid_deficit_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:58:24.852796+00:00
-- url     : https://prove2.me/submissions/15a451da-ff77-44bf-93cf-2b9ca9aa7375

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ExposureEntropy.lean:L109-L129
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.grid_deficit_decomposition. The node keeps its source
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

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma uniformDeficit_eq (P : Law α) :
    P.uniformDeficit = Real.log (Fintype.card α) - P.entropy := by
  simp [uniformDeficit, entropy, mean]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ExposureEntropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma grid_deficit_decomposition {A D : ℕ} (Q : Law (Grid A D)) :
    Q.uniformDeficit = (Q.map Prod.fst).uniformDeficit +
      (∑ k : Fin D, (Q.map (fun a => a.2 k)).uniformDeficit) +
        ((Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy) := by
  simp only [Law.uniformDeficit_eq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : Real.log (Fintype.card (Grid A D) : ℝ) =
      Real.log (Fintype.card (Rows A D) : ℝ) + D * Real.log (Fintype.card (Equiv.Perm (Fin A)) : ℝ) := by
    have h₁ : (Fintype.card (Rows A D) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have h₂ : ((Fintype.card (Equiv.Perm (Fin A)) : ℝ) ^ D) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
    change Real.log (Fintype.card (Rows A D × Cols A D) : ℝ) = _
    rw [Fintype.card_prod, Nat.cast_mul, Real.log_mul h₁ (by
      change (Fintype.card (Fin D → Equiv.Perm (Fin A)) : ℝ) ≠ 0
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
      exact h₂)]
    congr 1
    change Real.log (Fintype.card (Fin D → Equiv.Perm (Fin A)) : ℝ) = _
    rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  rw [hc]
  ring

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} (Q : Law (Grid A D)) :
    Q.uniformDeficit = (Q.map Prod.fst).uniformDeficit +
      (∑ k : Fin D, (Q.map (fun a => a.2 k)).uniformDeficit) +
        ((Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy) := by
  first
    | exact OAI.ThorpCompatibility.grid_deficit_decomposition Q
    | exact OAI.ThorpCompatibility.grid_deficit_decomposition
    | (apply OAI.ThorpCompatibility.grid_deficit_decomposition <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.grid_deficit_decomposition <;> assumption)
