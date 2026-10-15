-- Prove2me | solution 1 for OAI.ThorpCompatibility.Law.heavy_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:26:36.111266+00:00
-- url     : https://prove2.me/submissions/e85f322f-5644-4d16-a8c0-0dd71c6ad9f6

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/EntropyBounds.lean:L33-L60
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.Law.heavy_mass_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling

-- ---- from OAI.Probability.ThorpCompatibility.FiniteLaw ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

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

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.EntropyBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma heavy_mass_bound (P R : Law α) {H : ℝ} (hH : 0 < H)
    (hs : ∀ a, R.mass a = 0 → P.mass a = 0) :
    (Real.log H - 1) * P.prob (fun a => H * R.mass a < P.mass a) ≤
      P.relativeEntropy R := by
  have hterm (a : α) :
      (if H * R.mass a < P.mass a then P.mass a * (Real.log H - 1) else 0) +
        (P.mass a - R.mass a) ≤ P.mass a * Real.log (P.mass a / R.mass a) := by
    by_cases hh : H * R.mass a < P.mass a
    · rw [ite_eq_left hh]
      have hp : 0 < P.mass a := lt_of_le_of_lt (mul_nonneg hH.le (R.nonneg a)) hh
      have hq : 0 < R.mass a := lt_of_le_of_ne (R.nonneg a) (by
        intro h; exact hp.ne' (hs a h.symm))
      have hl : Real.log H ≤ Real.log (P.mass a / R.mass a) :=
        Real.log_le_log hH ((lt_div_iff₀ hq).mpr hh).le
      have hm := mul_le_mul_of_nonneg_left hl hp.le
      nlinarith [R.nonneg a]
    · rw [ite_eq_right hh, zero_add]
      exact pointwise_entropy_lower (P.nonneg a) (R.nonneg a) (hs a)
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hterm a
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, P.total, R.total,
    sub_self, add_zero] at hsum
  have he : (∑ a, if H * R.mass a < P.mass a then P.mass a * (Real.log H - 1) else 0) =
      (Real.log H - 1) * P.prob (fun a => H * R.mass a < P.mass a) := by
    rw [prob, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rwa [he] at hsum

end Law
end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility OAI.ThorpCompatibility.Law
open scoped Classical
open Finset
variable {α : Type*} [Fintype α]

theorem solution (P R : Law α) {H : ℝ} (hH : 0 < H)
    (hs : ∀ a, R.mass a = 0 → P.mass a = 0) :
    (Real.log H - 1) * P.prob (fun a => H * R.mass a < P.mass a) ≤
      P.relativeEntropy R := by
  first
    | exact OAI.ThorpCompatibility.Law.heavy_mass_bound P R hH hs
    | exact OAI.ThorpCompatibility.Law.heavy_mass_bound
    | (apply OAI.ThorpCompatibility.Law.heavy_mass_bound <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.Law.heavy_mass_bound <;> assumption)
