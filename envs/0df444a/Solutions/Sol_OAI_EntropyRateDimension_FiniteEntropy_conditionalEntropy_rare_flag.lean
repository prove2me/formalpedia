-- Prove2me | solution 1 for OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_rare_flag
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:31:32.228328+00:00
-- url     : https://prove2.me/submissions/646ace03-8fb2-419f-b506-eabe01edfbed

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L479-L516
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_rare_flag. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_conditionalEntropy_le_bad_mass
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem entropy_mixture {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (w : β → ℝ) (p : β → α → ℝ)
    (hw : ∀ b ∈ t, 0 ≤ w b) (hw1 : ∑ b ∈ t, w b = 1)
    (hp : ∀ b ∈ t, ∀ a ∈ s, 0 ≤ p b a) :
    ∑ b ∈ t, w b * entropy s (p b) ≤
      entropy s (fun a => ∑ b ∈ t, w b * p b a) := by
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  exact Real.concaveOn_negMulLog.le_map_sum hw hw1 (fun b hb => hp b hb a ha)

theorem entropy_joint_le {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b)
    (hp1 : ∑ a ∈ s, ∑ b ∈ t, p a b = 1) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) ≤
      entropy s (fun a => ∑ b ∈ t, p a b) + entropy t (fun b => ∑ a ∈ s, p a b) := by
  let r := fun a => ∑ b ∈ t, p a b
  have hr : ∀ a ∈ s, 0 ≤ r a := fun a ha => Finset.sum_nonneg (hp a ha)
  have hterm : ∀ a ∈ s, ∀ b ∈ t, r a * (p a b / r a) = p a b := by
    intro a ha b hb
    by_cases h : r a = 0
    · have hl := Finset.single_le_sum (hp a ha) hb
      have hz : p a b = 0 := le_antisymm (h ▸ hl) (hp a ha b hb)
      simp [hz]
    · exact mul_div_cancel₀ _ h
  have hc := entropy_mixture t s r (fun a b => p a b / r a) hr hp1
    (fun a ha b hb => div_nonneg (hp a ha b hb) (hr a ha))
  have hmix : entropy t (fun b => ∑ a ∈ s, r a * (p a b / r a)) =
      entropy t (fun b => ∑ a ∈ s, p a b) := by
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    exact Finset.sum_congr rfl (fun a ha => hterm a ha b hb)
  rw [hmix] at hc
  calc
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
        ∑ a ∈ s, entropy t (p a) := by simp only [entropy, Finset.sum_product]
    _ = entropy s r + ∑ a ∈ s, r a * entropy t (fun b => p a b / r a) := by
      simp only [entropy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      exact entropy_normalize t (p a) (hp a ha)
    _ ≤ _ := add_le_add le_rfl hc

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

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

theorem mass_pair_fst {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (b : β) :
    ∑ c ∈ s.image g, mass s p (fun a => (f a, g a)) (b, c) = mass s p f b := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hg : g a ∈ s.image g := Finset.mem_image_of_mem g ha
  by_cases hf : f a = b
  · simp [hf, hg]
  · simp [hf]

theorem mass_pair_snd {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) :
    ∑ b ∈ s.image f, mass s p (fun a => (f a, g a)) (b, c) = mass s p g c := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hf : f a ∈ s.image f := Finset.mem_image_of_mem f ha
  by_cases hg : g a = c
  · simp [hg, hf]
  · simp [hg]

theorem observableEntropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p (fun a => (f a, g a)) ≤
      observableEntropy s p f + observableEntropy s p g := by
  classical
  rw [observableEntropy_on_superset s (s.image f ×ˢ s.image g) p _
    (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f ha, Finset.mem_image_of_mem g ha⟩)]
  have h := entropy_joint_le (s.image f) (s.image g)
    (fun b c => mass s p (fun a => (f a, g a)) (b, c))
    (fun b _ c _ => mass_nonneg s p _ hp _) ?_
  · simpa only [mass_pair_fst, mass_pair_snd, observableEntropy] using h
  · simpa only [mass_pair_fst, mass_sum] using hp1

theorem conditionalEntropy_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f g ≤ observableEntropy s p f := by
  dsimp only [conditionalEntropy]
  linarith [observableEntropy_pair_le s p f g hp hp1]

theorem observableEntropy_equiv {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (e : β ≃ γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (e ∘ f) = observableEntropy s p f := by
  apply le_antisymm (observableEntropy_comp_le s p f e hp)
  have h := observableEntropy_comp_le s p (e ∘ f) e.symm hp
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

theorem conditionalEntropy_chain {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p (fun a => (f a, g a)) h =
      conditionalEntropy s p g h + conditionalEntropy s p f (fun a => (g a, h a)) := by
  have he := observableEntropy_equiv s p (fun a => ((f a, g a), h a))
    (Equiv.prodAssoc β γ δ) hp
  change observableEntropy s p (fun a => (f a, (g a, h a))) =
    observableEntropy s p (fun a => ((f a, g a), h a)) at he
  dsimp only [conditionalEntropy]
  linarith

theorem conditionalEntropy_reveal_le {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f h ≤ observableEntropy s p g +
      conditionalEntropy s p f (fun a => (g a, h a)) := by
  have hm := observableEntropy_comp_le s p (fun a => ((f a, g a), h a))
    (fun x => (x.1.1, x.2)) hp
  have hr := conditionalEntropy_chain s p f g h hp
  have hg := conditionalEntropy_le s p g h hp hp1
  dsimp only [conditionalEntropy] at *
  change observableEntropy s p (fun a => (f a, h a)) ≤ _ at hm
  linarith

theorem observableEntropy_bool {α : Type uα} (s : Finset α) (p : α → ℝ)
    (f : α → Bool) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f = Real.binEntropy (mass s p f true) := by
  have hsum := sum_mass_mul s Finset.univ p f (fun _ => 1) (fun _ _ => Finset.mem_univ _)
  have hm : mass s p f false = 1 - mass s p f true := by
    simp only [mul_one, Fintype.sum_bool, hp1] at hsum
    linarith
  rw [observableEntropy_on_superset s Finset.univ p f (fun _ _ => Finset.mem_univ _)]
  simp only [entropy, Fintype.sum_bool, hm,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem conditionalEntropy_rare_flag {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (C : α → β) (Y : α → γ) (E : α → Bool)
    (B : γ → Prop) [DecidablePred B] (c₀ : β)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1)
    (hgood : ∀ a ∈ s, E a = false → ¬B (Y a) → C a = c₀) :
    conditionalEntropy s p C Y ≤ Real.binEntropy (mass s p E true) +
      (mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a) *
        Real.log (s.image C).card := by
  classical
  let bad : Bool × γ → Prop := fun ey => ey.1 = true ∨ B ey.2
  have hc := conditionalEntropy_le_bad_mass s p C (fun a => (E a, Y a)) bad hp ?_
  · have hn : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hp1
      norm_num at hp1
    have hK : 0 ≤ Real.log (s.image C).card := Real.log_nonneg (by
      exact_mod_cast Finset.card_pos.mpr (hn.image C))
    have hb : (∑ a ∈ s, if bad (E a, Y a) then p a else 0) ≤
        mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a := by
      simp only [mass, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a ha
      dsimp only [bad]
      split_ifs <;> first | linarith [hp a ha] | simp_all
    have hm := mul_le_mul_of_nonneg_right hb hK
    have hr := conditionalEntropy_reveal_le s p C E Y hp hp1
    rw [observableEntropy_bool s p E hp1] at hr
    linarith
  · intro a ha b hb he hbad
    have hEa : E a = false := by
      have : E a ≠ true := fun h => hbad (Or.inl h)
      cases h : E a <;> simp_all
    have hBa : ¬B (Y a) := fun h => hbad (Or.inr h)
    have hEb : E b = false := (congrArg Prod.fst he).symm.trans hEa
    have hBb : ¬B (Y b) := by
      simpa only [show Y b = Y a from (congrArg Prod.snd he).symm] using hBa
    rw [hgood a ha hEa hBa, hgood b hb hEb hBb]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uα,uβ,uγ} : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_rare_flag.{uα,uβ,uγ} := @_root_.OAI.EntropyRateDimension.FiniteEntropy.conditionalEntropy_rare_flag.{uα,uβ,uγ}
