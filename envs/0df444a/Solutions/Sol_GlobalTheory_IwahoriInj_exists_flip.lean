-- Prove2me | solution 1 for GlobalTheory.IwahoriInj.exists_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:27.143351+00:00
-- url     : https://prove2.me/submissions/12eedf36-6e7f-437a-8fc7-155a7b56ad22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {n : Type}
namespace GlobalTheory.IwahoriInj
theorem _root_.solution {f : n → n → ℤ} (hf : Chamber f) {i j : n} (hij : i ≠ j)
    (hw : ∀ l, l ≠ i → l ≠ j → f j i < f j l + f l i) :
    ∃ g f' : n → n → ℤ, Conc g ∧ Chamber f' ∧ f i j = g i j + 1 ∧
      (∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b) ∧ f' j i = g j i + 1 ∧
      (∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b) := by
  classical
  let g : n → n → ℤ := fun a b => if a = i ∧ b = j then f a b - 1 else f a b
  let f' : n → n → ℤ := fun a b => if a = j ∧ b = i then g a b + 1 else g a b
  have g1 : f i j = g i j + 1 := by simp [g]
  have g2 : ∀ a b, ¬ (a = i ∧ b = j) → f a b = g a b := fun a b h => by simp only [g, if_neg h]
  have f1 : f' j i = g j i + 1 := by simp [f']
  have f2 : ∀ a b, ¬ (a = j ∧ b = i) → f' a b = g a b := fun a b h => by simp only [f', if_neg h]
  have gle : ∀ a b, g a b ≤ f a b := fun a b => by simp only [g]; split_ifs <;> omega
  have fle : ∀ a b, g a b ≤ f' a b := fun a b => by simp only [f']; split_ifs <;> omega
  clear_value f' g
  obtain ⟨⟨h0, h1⟩, h2⟩ := hf
  have h3 := h2 i j hij
  have hg0 : ∀ a, g a a = 0 := fun a => by rw [← g2 a a (by grind), h0]
  have hg : Conc g := by
    refine ⟨hg0, fun a b l => ?_⟩
    by_cases c1 : a = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := c1
      have := g2 l b (by grind)
      by_cases c : b = l
      · subst c; have := hg0 b; omega
      by_cases c' : b = a
      · subst c'; have := hg0 b; omega
      have := hw b c' c; have := h2 b a c'; have := gle a b; omega
    by_cases c2 : l = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := c2
      have := g2 a l (by grind)
      by_cases c : a = l
      · subst c; have := hg0 a; omega
      by_cases c' : a = b
      · subst c'; have := hg0 a; omega
      have := hw a c c'; have := h2 a b c'; have := gle a b; omega
    have := g2 a l c1; have := g2 l b c2; have := gle a b; have := h1 a b l; omega
  have hf0 : ∀ a, f' a a = 0 := fun a => by rw [f2 a a (by grind), hg0]
  refine ⟨g, f', hg, ⟨⟨hf0, fun a b l => ?_⟩, fun a b hab => ?_⟩, g1, g2, f1, f2⟩
  · by_cases c1 : a = j ∧ b = i
    · obtain ⟨rfl, rfl⟩ := c1
      by_cases c : l = b
      · subst c; have := hf0 l; omega
      by_cases c' : l = a
      · subst c'; have := hf0 l; omega
      have := hw l c c'; have := fle a l; have := fle l b
      have := g2 a b (by grind); have := g2 a l (by grind); have := g2 l b (by grind); omega
    have := f2 a b c1; have := hg.2 a b l; have := fle a l; have := fle l b; omega
  · have := g2 j i (by grind)
    have := f2 i j (by grind)
    by_cases c1 : a = j ∧ b = i
    · obtain ⟨rfl, rfl⟩ := c1; omega
    by_cases c2 : a = i ∧ b = j
    · obtain ⟨rfl, rfl⟩ := c2; omega
    have := f2 a b c1; have := f2 b a (by grind); have := g2 a b c2; have := g2 b a (by grind)
    have := h2 a b hab; omega
end GlobalTheory.IwahoriInj
