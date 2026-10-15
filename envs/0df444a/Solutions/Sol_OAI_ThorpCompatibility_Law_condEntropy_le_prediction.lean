-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.condEntropy_le_prediction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:23:52.70427+00:00
-- url     : https://prove2.me/submissions/fc7050e8-6f06-4e51-a95f-45c9bccd4d24

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ConditionalEntropy.lean:L34-L64
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.condEntropy_le_prediction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_eq_mean
import Theorems.Thm_OAI_ThorpCompatibility_Law_map_mass_pos_iff

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

lemma pointwise_entropy_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) : p - q ≤ p * Real.log (p / q) := by
  by_cases hq0 : q = 0
  · simp [hq0, hzero hq0]
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  calc
    p - q = q * (p / q - 1) := by field_simp
    _ ≤ q * (p / q * Real.log (p / q)) := h
    _ = p * Real.log (p / q) := by field_simp

lemma relativeEntropy_nonneg (P Q : Law α)
    (hzero : ∀ a, Q.mass a = 0 → P.mass a = 0) :
    0 ≤ P.relativeEntropy Q := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    pointwise_entropy_lower (P.nonneg a) (Q.nonneg a) (hzero a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, P.total, Q.total] using h

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

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ConditionalEntropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma condEntropy_le_prediction (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (hs : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a)) :
    P.condEntropy X Y ≤ -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) := by
  let J := P.map (fun a => (X a, Y a))
  let R := (P.map Y).kernelJoint K
  have hzero : ∀ b, R.mass b = 0 → J.mass b = 0 := by
    intro b hb
    by_contra hJ
    have hpos : 0 < J.mass b := lt_of_le_of_ne (J.nonneg b) (Ne.symm hJ)
    obtain ⟨a, ha, hPa⟩ := (P.map_mass_pos_iff (fun a => (X a, Y a)) b).mp hpos
    have hR : 0 < R.mass (X a, Y a) :=
      mul_pos (P.map_mass_pos Y hPa) (hs a hPa)
    rw [ha, hb] at hR
    exact lt_irrefl _ hR
  have h := J.relativeEntropy_nonneg R hzero
  have hmean : J.relativeEntropy R =
      P.mean (fun a => Real.log (P.condMass X Y a)) -
        P.mean (fun a => Real.log ((K (Y a)).mass (X a))) := by
    change J.mean (fun b => Real.log (J.mass b / R.mass b)) = _
    rw [P.mean_map, ← P.mean_sub]
    apply P.mean_congr_support
    intro a ha
    dsimp [J, R, kernelJoint, Function.comp_def, condMass]
    rw [Real.log_div (P.map_mass_pos _ ha).ne'
      (mul_pos (P.map_mass_pos Y ha) (hs a ha)).ne',
      Real.log_mul (P.map_mass_pos Y ha).ne' (hs a ha).ne',
      Real.log_div (P.map_mass_pos _ ha).ne' (P.map_mass_pos Y ha).ne']
    ring
  rw [hmean] at h
  rw [P.condEntropy_eq_mean]
  linarith

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem solution (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (hs : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a)) :
    P.condEntropy X Y ≤ -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) := by
  first
    | exact OAI.ThorpCompatibility.Law.condEntropy_le_prediction P X Y K hs
    | exact OAI.ThorpCompatibility.Law.condEntropy_le_prediction
    | (apply OAI.ThorpCompatibility.Law.condEntropy_le_prediction <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.condEntropy_le_prediction <;> assumption)
