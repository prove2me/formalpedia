-- Prove2me | solution 1 for JeroslowMLP.Value.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:21:50.505775+00:00
-- url     : https://prove2.me/submissions/c8823b65-4ccb-4355-95a6-a2fe04ba42ab

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Formula
import Definitions.Def_JeroslowMLP_Value_Multilevel

set_option autoImplicit false
open JeroslowMLP.Value

lemma JML31_and (v vG vH : ℝ) (b c : Bool) (hv : v = 0 ∨ v = 1)
    (hG : vG = if b = true then 1 else 0) (hH : vH = if c = true then 1 else 0)
    (h1 : v ≤ vG) (h2 : v ≤ vH) (h3 : vG + vH - 1 ≤ v) :
    v = if (b && c) = true then 1 else 0 := by
  cases b <;> cases c <;> simp at hG hH ⊢ <;> subst hG <;> subst hH <;> rcases hv with h | h <;>
    first | exact h | (exfalso; linarith) | skip
  all_goals (first | exact h | (exfalso; linarith))

lemma JML31_or (v vG vH : ℝ) (b c : Bool) (hv : v = 0 ∨ v = 1)
    (hG : vG = if b = true then 1 else 0) (hH : vH = if c = true then 1 else 0)
    (h1 : v ≤ vG + vH) (h2 : vG ≤ v) (h3 : vH ≤ v) :
    v = if (b || c) = true then 1 else 0 := by
  cases b <;> cases c <;> simp at hG hH ⊢ <;> subst hG <;> subst hH <;> rcases hv with h | h <;>
    first | exact h | (exfalso; linarith) | skip
  all_goals (first | exact h | (exfalso; linarith))

lemma JML31_and_ex (b c : Bool) :
    (if (b && c) = true then (1:ℝ) else 0) ≤ (if b = true then 1 else 0) ∧
    (if (b && c) = true then (1:ℝ) else 0) ≤ (if c = true then 1 else 0) ∧
    (if b = true then (1:ℝ) else 0) + (if c = true then 1 else 0) - 1 ≤
      (if (b && c) = true then (1:ℝ) else 0) ∧
    0 ≤ (if (b && c) = true then (1:ℝ) else 0) ∧ (if (b && c) = true then (1:ℝ) else 0) ≤ 1 := by
  cases b <;> cases c <;> norm_num

lemma JML31_or_ex (b c : Bool) :
    (if (b || c) = true then (1:ℝ) else 0) ≤ (if b = true then (1:ℝ) else 0) + (if c = true then 1 else 0) ∧
    (if b = true then (1:ℝ) else 0) ≤ (if (b || c) = true then 1 else 0) ∧
    (if c = true then (1:ℝ) else 0) ≤ (if (b || c) = true then 1 else 0) ∧
    0 ≤ (if (b || c) = true then (1:ℝ) else 0) ∧ (if (b || c) = true then (1:ℝ) else 0) ≤ 1 := by
  cases b <;> cases c <;> norm_num

lemma JML31_main {β : Type} (xa : β → ℝ) (α : β → Bool) (hxa : ∀ a, xa a = if α a = true then 1 else 0) :
    ∀ G : Formula β,
      (∀ w : G.Node → ℝ, (∀ g, IsBinary (w g)) → G.LSys xa w →
        G.nodeVal xa w = if G.eval α = true then 1 else 0) ∧
      (∀ w w' : G.Node → ℝ, (∀ g, IsBinary (w g)) → G.LSys xa w →
        (∀ g, IsBinary (w' g)) → G.LSys xa w' → w = w') ∧
      (∃ w : G.Node → ℝ, (∀ g, IsBinary (w g)) ∧ G.LSys xa w) := by
  intro G
  induction G with
  | var a =>
    refine ⟨?_, ?_, ?_⟩
    · intro w _ _
      show xa a = if α a = true then 1 else 0
      exact hxa a
    · intro w w' _ _ _ _
      funext g
      exact g.elim
    · refine ⟨fun g => g.elim, fun g => g.elim, ?_⟩
      show 0 ≤ xa a ∧ xa a ≤ 1
      rw [hxa a]
      cases α a <;> simp
  | neg G ih =>
    obtain ⟨S, U, E⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro w hb hs
      obtain ⟨hG, hx, h0, h1⟩ := hs
      have := S (fun g => w (some g)) (fun g => hb (some g)) hG
      show w none = if (!G.eval α) = true then 1 else 0
      rw [hx]
      show 1 - G.nodeVal xa (fun g => w (some g)) = _
      rw [this]
      cases G.eval α <;> simp
    · intro w w' hb hs hb' hs'
      obtain ⟨hG, hx, h0, h1⟩ := hs
      obtain ⟨hG', hx', h0', h1'⟩ := hs'
      have e1 := S (fun g => w (some g)) (fun g => hb (some g)) hG
      have e2 := S (fun g => w' (some g)) (fun g => hb' (some g)) hG'
      have e3 := U _ _ (fun g => hb (some g)) hG (fun g => hb' (some g)) hG'
      funext o
      rcases o with _ | g
      · show w none = w' none
        rw [hx, hx']
        show 1 - G.nodeVal xa (fun g => w (some g)) = 1 - G.nodeVal xa (fun g => w' (some g))
        rw [e1, e2]
      · exact congrFun e3 g
    · obtain ⟨w₀, hb, hs⟩ := E
      refine ⟨fun o => o.elim (1 - (if G.eval α = true then 1 else 0)) w₀, ?_, ?_⟩
      · intro o
        rcases o with _ | g
        · show IsBinary (1 - (if G.eval α = true then 1 else 0))
          cases G.eval α <;> simp [IsBinary]
        · exact hb g
      · have := S w₀ hb hs
        refine ⟨hs, ?_, ?_, ?_⟩
        · show 1 - (if G.eval α = true then 1 else 0) = 1 - G.nodeVal xa w₀
          rw [this]
        · show 0 ≤ 1 - (if G.eval α = true then (1:ℝ) else 0)
          cases G.eval α <;> simp
        · show 1 - (if G.eval α = true then (1:ℝ) else 0) ≤ 1
          cases G.eval α <;> simp
  | and G H ihG ihH =>
    obtain ⟨SG, UG, EG⟩ := ihG
    obtain ⟨SH, UH, EH⟩ := ihH
    have Sc : ∀ w : (Formula.and G H).Node → ℝ, (∀ g, IsBinary (w g)) →
        (Formula.and G H).LSys xa w →
        w none = if (G.eval α && H.eval α) = true then 1 else 0 := by
      intro w hb hs
      obtain ⟨hG, hH, hxG, hxH, hxs, h0, h1⟩ := hs
      have e1 := SG (fun g => w (some (Sum.inl g))) (fun g => hb _) hG
      have e2 := SH (fun g => w (some (Sum.inr g))) (fun g => hb _) hH
      exact JML31_and (w none) _ _ _ _ (hb none) e1 e2 hxG hxH hxs
    refine ⟨?_, ?_, ?_⟩
    · intro w hb hs
      exact Sc w hb hs
    · intro w w' hb hs hb' hs'
      have sw := Sc w hb hs
      have sw' := Sc w' hb' hs'
      obtain ⟨hG, hH, hxG, hxH, hxs, h0, h1⟩ := hs
      obtain ⟨hG', hH', -⟩ := hs'
      have e3 := UG _ _ (fun g => hb _) hG (fun g => hb' _) hG'
      have e4 := UH _ _ (fun g => hb _) hH (fun g => hb' _) hH'
      funext o
      rcases o with _ | (g | g)
      · rw [sw, sw']
      · exact congrFun e3 g
      · exact congrFun e4 g
    · obtain ⟨wG, hbG, hsG⟩ := EG
      obtain ⟨wH, hbH, hsH⟩ := EH
      have vG := SG wG hbG hsG
      have vH := SH wH hbH hsH
      obtain ⟨a1, a2, a3, a4, a5⟩ := JML31_and_ex (G.eval α) (H.eval α)
      refine ⟨fun o => o.elim (if (G.eval α && H.eval α) = true then 1 else 0) (Sum.elim wG wH), ?_, ?_⟩
      · intro o
        rcases o with _ | (g | g)
        · show IsBinary (if (G.eval α && H.eval α) = true then 1 else 0)
          cases G.eval α <;> cases H.eval α <;> simp [IsBinary]
        · exact hbG g
        · exact hbH g
      · refine ⟨hsG, hsH, ?_, ?_, ?_, ?_, ?_⟩
        · show (if (G.eval α && H.eval α) = true then (1:ℝ) else 0) ≤ G.nodeVal xa wG
          rw [vG]; exact a1
        · show (if (G.eval α && H.eval α) = true then (1:ℝ) else 0) ≤ H.nodeVal xa wH
          rw [vH]; exact a2
        · show G.nodeVal xa wG + H.nodeVal xa wH - 1 ≤ (if (G.eval α && H.eval α) = true then (1:ℝ) else 0)
          rw [vG, vH]; exact a3
        · exact a4
        · exact a5
  | or G H ihG ihH =>
    obtain ⟨SG, UG, EG⟩ := ihG
    obtain ⟨SH, UH, EH⟩ := ihH
    have Sc : ∀ w : (Formula.or G H).Node → ℝ, (∀ g, IsBinary (w g)) →
        (Formula.or G H).LSys xa w →
        w none = if (G.eval α || H.eval α) = true then 1 else 0 := by
      intro w hb hs
      obtain ⟨hG, hH, hxs, hxG, hxH, h0, h1⟩ := hs
      have e1 := SG (fun g => w (some (Sum.inl g))) (fun g => hb _) hG
      have e2 := SH (fun g => w (some (Sum.inr g))) (fun g => hb _) hH
      exact JML31_or (w none) _ _ _ _ (hb none) e1 e2 hxs hxG hxH
    refine ⟨?_, ?_, ?_⟩
    · intro w hb hs
      exact Sc w hb hs
    · intro w w' hb hs hb' hs'
      have sw := Sc w hb hs
      have sw' := Sc w' hb' hs'
      obtain ⟨hG, hH, hxs, hxG, hxH, h0, h1⟩ := hs
      obtain ⟨hG', hH', -⟩ := hs'
      have e3 := UG _ _ (fun g => hb _) hG (fun g => hb' _) hG'
      have e4 := UH _ _ (fun g => hb _) hH (fun g => hb' _) hH'
      funext o
      rcases o with _ | (g | g)
      · rw [sw, sw']
      · exact congrFun e3 g
      · exact congrFun e4 g
    · obtain ⟨wG, hbG, hsG⟩ := EG
      obtain ⟨wH, hbH, hsH⟩ := EH
      have vG := SG wG hbG hsG
      have vH := SH wH hbH hsH
      obtain ⟨a1, a2, a3, a4, a5⟩ := JML31_or_ex (G.eval α) (H.eval α)
      refine ⟨fun o => o.elim (if (G.eval α || H.eval α) = true then 1 else 0) (Sum.elim wG wH), ?_, ?_⟩
      · intro o
        rcases o with _ | (g | g)
        · show IsBinary (if (G.eval α || H.eval α) = true then 1 else 0)
          cases G.eval α <;> cases H.eval α <;> simp [IsBinary]
        · exact hbG g
        · exact hbH g
      · refine ⟨hsG, hsH, ?_, ?_, ?_, ?_, ?_⟩
        · show (if (G.eval α || H.eval α) = true then (1:ℝ) else 0) ≤ G.nodeVal xa wG + H.nodeVal xa wH
          rw [vG, vH]; exact a1
        · show G.nodeVal xa wG ≤ (if (G.eval α || H.eval α) = true then (1:ℝ) else 0)
          rw [vG]; exact a2
        · show H.nodeVal xa wH ≤ (if (G.eval α || H.eval α) = true then (1:ℝ) else 0)
          rw [vH]; exact a3
        · exact a4
        · exact a5

theorem solution (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) (α : Atom p n → Bool) :
    (∃! w : F.Node → ℝ, (∀ g, IsBinary (w g)) ∧
        F.LSys (fun a => if α a then 1 else 0) w) ∧
    ∀ w : F.Node → ℝ, (∀ g, IsBinary (w g)) →
      F.LSys (fun a => if α a then 1 else 0) w →
      (F.eval α = true ↔ F.nodeVal (fun a => if α a then 1 else 0) w = 1) := by
  obtain ⟨S, U, ⟨w₀, hb, hs⟩⟩ := JML31_main (fun a => if α a then (1:ℝ) else 0) α (fun a => rfl) F
  refine ⟨⟨w₀, ⟨hb, hs⟩, fun w' ⟨hb', hs'⟩ => U _ _ hb' hs' hb hs⟩, ?_⟩
  intro w hbw hsw
  rw [S w hbw hsw]
  cases F.eval α <;> simp
