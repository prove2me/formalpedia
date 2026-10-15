-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.heavy_mass_uniformOn
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:01:10.429798+00:00
-- url     : https://prove2.me/submissions/fcc54550-cad9-4fc8-9580-a66b6a8b87f0

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/UniformSupport.lean:L43-L61
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.heavy_mass_uniformOn. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_Law_heavy_mass_bound

-- ---- from OAI.Probability.ThorpCompatibility.UniformSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma entropy_uniformOn_comparison (P : Law α) (s : Finset α) (hs : s.Nonempty)
    (hz : ∀ a, a ∉ s → P.mass a = 0) :
    P.relativeEntropy (uniformOn s hs) = Real.log (s.card : ℝ) - P.entropy := by
  have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  have hterm (a : α) : P.mass a * Real.log (P.mass a / (uniformOn s hs).mass a) =
      P.mass a * Real.log (P.mass a) + P.mass a * Real.log (s.card : ℝ) := by
    by_cases hp : P.mass a = 0
    · simp [hp]
    have ha : a ∈ s := by by_contra h; exact hp (hz a h)
    simp only [uniformOn, ite_eq_left ha, one_div, div_inv_eq_mul,
      Real.log_mul hp hc, mul_add]
  simp_rw [relativeEntropy, hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.total, one_mul]
  unfold entropy mean
  ring

lemma heavy_mass_uniformOn (P : Law α) (s : Finset α) (hs : s.Nonempty)
    (hz : ∀ a, a ∉ s → P.mass a = 0) {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * P.prob (fun a => H / (s.card : ℝ) < P.mass a) ≤
      Real.log (s.card : ℝ) - P.entropy := by
  have hzero : ∀ a, (uniformOn s hs).mass a = 0 → P.mass a = 0 := by
    intro a h
    by_cases ha : a ∈ s
    · simp [uniformOn, ha, hs.card_ne_zero] at h
    · exact hz a ha
  have h := P.heavy_mass_bound (uniformOn s hs) hH hzero
  rw [P.entropy_uniformOn_comparison s hs hz] at h
  convert h using 2
  congr 1
  funext a
  apply propext
  by_cases ha : a ∈ s
  · simp [uniformOn, ha, div_eq_mul_inv]
  · have hb : 0 ≤ H / (s.card : ℝ) := div_nonneg hH.le (Nat.cast_nonneg _)
    simp [uniformOn, ha, hz a ha, not_lt.mpr hb]

end Law
open Finset

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem solution (P : Law α) (s : Finset α) (hs : s.Nonempty)
    (hz : ∀ a, a ∉ s → P.mass a = 0) {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * P.prob (fun a => H / (s.card : ℝ) < P.mass a) ≤
      Real.log (s.card : ℝ) - P.entropy := by
  first
    | exact OAI.ThorpCompatibility.Law.heavy_mass_uniformOn P s hs hz hH
    | exact OAI.ThorpCompatibility.Law.heavy_mass_uniformOn
    | (apply OAI.ThorpCompatibility.Law.heavy_mass_uniformOn <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.heavy_mass_uniformOn <;> assumption)
