-- Prove2me | solution 1 for OAI.ThorpCompatibility.compatibilityWeight_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:12:10.867857+00:00
-- url     : https://prove2.me/submissions/4011f785-2223-4fb9-829a-caf3b38d6e0b

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/VariationalBound.lean:L45-L65
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.compatibilityWeight_support. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_VariationalBound

-- ---- from OAI.Probability.ThorpCompatibility.VariationalBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma compatibilityWeight_support {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    {a : Grid A D} (ha : 0 < compatibilityWeight w v a) :
    Compatible a.1 a.2 ∧ (∀ i, 0 < w i (a.1 i)) ∧ (∀ k, 0 < v k (a.2 k)) := by
  have hc : Compatible a.1 a.2 := by
    by_contra h
    simp [compatibilityWeight, h] at ha
  rw [compatibilityWeight, ite_eq_left hc] at ha
  refine ⟨hc, ?_, ?_⟩
  · intro i
    apply lt_of_le_of_ne (hw i _)
    intro he
    have hz : (∏ j : Fin A, w j (a.1 j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) he.symm
    simp [hz] at ha
  · intro k
    apply lt_of_le_of_ne (hv k _)
    intro he
    have hz : (∏ j : Fin D, v j (a.2 j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ k) he.symm
    simp [hz] at ha

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    {a : Grid A D} (ha : 0 < compatibilityWeight w v a) :
    Compatible a.1 a.2 ∧ (∀ i, 0 < w i (a.1 i)) ∧ (∀ k, 0 < v k (a.2 k)) := by
  first
    | exact OAI.ThorpCompatibility.compatibilityWeight_support w v hw hv ha
    | exact OAI.ThorpCompatibility.compatibilityWeight_support
    | (apply OAI.ThorpCompatibility.compatibilityWeight_support <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.compatibilityWeight_support <;> assumption)
