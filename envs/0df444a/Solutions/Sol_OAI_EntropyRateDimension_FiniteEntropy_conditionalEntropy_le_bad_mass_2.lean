-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:29:54.378338+00:00
-- url     : https://prove2.me/submissions/a1d3c7bc-b4d2-459f-8893-6df2dc08ef0c

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L424-L466
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_eq_sum
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

theorem observableEntropy_const_of {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (b : β) (hf : ∀ a ∈ s, f a = b) :
    observableEntropy s p f = Real.negMulLog (∑ a ∈ s, p a) := by
  classical
  rw [observableEntropy_on_superset s {b} p f (fun a ha => Finset.mem_singleton.mpr (hf a ha))]
  simp only [entropy, Finset.sum_singleton, mass]
  rw [Finset.filter_eq_self.mpr hf]

theorem observableEntropy_le_log_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f ≤ Real.log t.card := by
  rw [observableEntropy_on_superset s t p f hf]
  apply entropy_le_log_card _ _ (fun b _ => mass_nonneg s p f hp b)
  have h := sum_mass_mul s t p f (fun _ => 1) hf
  simpa only [mul_one, hp1] using h

theorem conditionalEntropy_le_bad_mass {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (bad : γ → Prop) [DecidablePred bad] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hgood : ∀ a ∈ s, ∀ b ∈ s, g a = g b → ¬bad (g a) → f a = f b) :
    conditionalEntropy s p f g ≤
      (∑ a ∈ s, if bad (g a) then p a else 0) * Real.log (s.image f).card := by
  classical
  let K := Real.log (s.image f).card
  rw [conditionalEntropy_eq_sum s p f g hp]
  calc
    _ ≤ ∑ c ∈ s.image g, mass s p g c * (if bad c then K else 0) := by
      apply Finset.sum_le_sum
      intro c hc
      let P := mass s p g c
      have hP : 0 ≤ P := mass_nonneg s p g hp c
      by_cases hP0 : P = 0
      · change P * _ ≤ P * _
        simp only [hP0, zero_mul, le_refl]
      have hn : ∑ a ∈ s.filter (fun a => g a = c), p a / P = 1 := by
        rw [← Finset.sum_div]
        exact div_self hP0
      have hq : ∀ a ∈ s.filter (fun a => g a = c), 0 ≤ p a / P :=
        fun a ha => div_nonneg (hp a (Finset.mem_filter.mp ha).1) hP
      apply mul_le_mul_of_nonneg_left _ hP
      by_cases hbad : bad c
      · rw [ite_eq_left hbad]
        exact observableEntropy_le_log_on_superset _ (s.image f) _ f
          (fun a ha => Finset.mem_image_of_mem f (Finset.mem_filter.mp ha).1) hq hn
      · rw [ite_eq_right hbad]
        obtain ⟨a₀, ha₀, hga₀⟩ := Finset.mem_image.mp hc
        have hconst : ∀ a ∈ s.filter (fun a => g a = c), f a = f a₀ := by
          intro a ha
          obtain ⟨has, hga⟩ := Finset.mem_filter.mp ha
          exact hgood a has a₀ ha₀ (hga.trans hga₀.symm) (hga ▸ hbad)
        rw [observableEntropy_const_of _ _ _ (f a₀) hconst, hn, Real.negMulLog_one]
    _ = ∑ a ∈ s, p a * (if bad (g a) then K else 0) :=
      sum_mass_mul s (s.image g) p g _ (fun a ha => Finset.mem_image_of_mem g ha)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp [K]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα,uβ,uγ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass.{uα,uβ,uγ} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_le_bad_mass.{uα,uβ,uγ}
