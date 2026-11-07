-- Prove2me | solution 1 for JeroslowMLP.Value.eq_4_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:00:56.025326+00:00
-- url     : https://prove2.me/submissions/3fe3c691-4e14-435b-adc9-3a4afc1c9b6c

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game
import Theorems.Thm_JeroslowMLP_Value_eq_4_2

set_option autoImplicit false
open JeroslowMLP.Value MultilevelProgram GVar
open scoped Classical

namespace JML43

variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

lemma solSet_anti (G : MultilevelProgram (GVar p n F)) (j m : ℕ) (h : j ≤ m) :
    G.solSet m ⊆ G.solSet j := by
  induction m with
  | zero => obtain rfl : j = 0 := by omega
            exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_ge j (m + 1) with h' | h'
    · exact fun x hx => ih (by omega) hx.1
    · obtain rfl : j = m + 1 := by omega
      exact le_rfl

/-- Flip `y ↦ 1 - y` on every gadget in `σ` whose argument equals `1`. -/
noncomputable def flipY (σ : {a : Atom p n // 1 ≤ a.1.val} → Bool → Prop)
    (x : GVar p n F → ℝ) : GVar p n F → ℝ
  | gy g s => if σ g s ∧ gArg x g s = 1 then 1 - x (gy g s) else x (gy g s)
  | atom a => x (atom a)
  | node g => x (node g)
  | one => x one
  | gz g s => x (gz g s)
  | fz a => x (fz a)
  | fzF => x fzF

variable (σ : {a : Atom p n // 1 ≤ a.1.val} → Bool → Prop)

lemma flipY_ne (x : GVar p n F → ℝ) (v : GVar p n F) (hv : ∀ g s, v ≠ gy g s) :
    flipY σ x v = x v := by
  cases v with
  | gy g s => exact absurd rfl (hv g s)
  | _ => rfl

lemma flipY_gArg (x : GVar p n F → ℝ) (g s) : gArg (flipY σ x) g s = gArg x g s := by
  unfold gArg; rw [flipY_ne σ x _ (by simp)]

lemma flipY_xF (x : GVar p n F → ℝ) : xF (flipY σ x) = xF x := by
  unfold xF
  have e1 : (fun a => flipY σ x (atom a)) = fun a => x (atom a) := rfl
  have e2 : (fun g => flipY σ x (node g)) = fun g => x (node g) := rfl
  rw [e1, e2]

lemma flipY_feas (x : GVar p n F → ℝ) (hx : x ∈ jFeasible p n F) :
    flipY σ x ∈ jFeasible p n F := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hx
  refine ⟨c1, c2, c3, ?_, c5, ?_⟩
  · intro g s
    rw [flipY_gArg]
    show 2 * flipY σ x (gy g s) - gArg x g s ≤ x (gz g s) ∧
      -(2 * flipY σ x (gy g s) - gArg x g s) ≤ x (gz g s) ∧
      0 ≤ flipY σ x (gy g s) ∧ flipY σ x (gy g s) ≤ 1
    obtain ⟨d1, d2, d3, d4⟩ := c4 g s
    simp only [flipY]
    split_ifs with h
    · rw [h.2] at d1 d2 ⊢
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩
    · exact ⟨d1, d2, d3, d4⟩
  · rw [flipY_xF]; exact c6

lemma flipY_crit (i : ℕ) (hσ : ∀ g s, σ g s → jCost p n F i (gy g s) = 0)
    (x : GVar p n F → ℝ) : (jGame p n F).crit i (flipY σ x) = (jGame p n F).crit i x := by
  unfold MultilevelProgram.crit
  apply Finset.sum_congr rfl
  intro v _
  cases v with
  | gy g s =>
    show jCost p n F i (gy g s) * flipY σ x (gy g s) = jCost p n F i (gy g s) * x (gy g s)
    simp only [flipY]
    split_ifs with h
    · rw [hσ g s h.1]; ring
    · rfl
  | _ => rfl

lemma flipY_agree (j : ℕ) (x x' : GVar p n F → ℝ)
    (h : ∀ v, j < jOwner v → x' v = flipY σ x v) :
    ∀ v, j < jOwner v → flipY σ x' v = x v := by
  intro v hv
  cases v with
  | gy g s =>
    have hA : ∀ a, x' (atom a) = x (atom a) := by
      intro a; rw [h (atom a) (by show j < a.1.val + 1; have : j < 1 := hv; omega)]; rfl
    have hg : gArg x' g s = gArg x g s := by unfold gArg; rw [hA]
    have hy := h (gy g s) hv
    simp only [flipY] at hy ⊢
    rw [hg, hy]
    split_ifs <;> ring
  | _ => rw [flipY_ne σ x' _ (by simp)]; rw [h _ hv]; rfl

lemma flipY_solSet (j : ℕ) (hσ : ∀ i < j, ∀ g s, σ g s → jCost p n F i (gy g s) = 0)
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet j) :
    flipY σ x ∈ (jGame p n F).solSet j := by
  induction j generalizing x with
  | zero => exact flipY_feas σ x hx
  | succ j ih =>
    have ih' := fun y hy => ih (fun i hi => hσ i (by omega)) y hy
    refine ⟨ih' x hx.1, ?_⟩
    intro x' hx' hag
    have h2 := hx.2 (flipY σ x') (ih' x' hx') (flipY_agree σ j x x' hag)
    rw [flipY_crit σ j (hσ j (by omega))] at h2
    rw [flipY_crit σ j (hσ j (by omega))]
    exact h2

end JML43

open JML43

theorem solution (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) (k : Fin p) (hk : 1 ≤ k.val)
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet (k.val + 2)) (j : Fin (n k)) :
    (∀ s : Bool, x (gy ⟨⟨k, j⟩, hk⟩ s) = if gArg x ⟨⟨k, j⟩, hk⟩ s < 1 then 1 else 0) ∧
    x (gy ⟨⟨k, j⟩, hk⟩ false) + x (gy ⟨⟨k, j⟩, hk⟩ true) =
      if x (atom ⟨k, j⟩) = 0 ∨ x (atom ⟨k, j⟩) = 1 then 1 else 2 := by
  set g0 : {a : Atom p n // 1 ≤ a.1.val} := ⟨⟨k, j⟩, hk⟩ with hg0
  have hg01 : g0.1 = ⟨k, j⟩ := rfl
  have hx2 : x ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ (by omega) hx
  have hfe : x ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hx
  have hat := hfe.1 ⟨k, j⟩
  obtain ⟨i, hi⟩ : ∃ i, k.val = i + 1 := ⟨k.val - 1, by omega⟩
  have part1 : ∀ s : Bool, x (gy g0 s) = if gArg x g0 s < 1 then 1 else 0 := by
    intro s
    have h42 := JeroslowMLP.Value.eq_4_2 p n F x hx2 g0 s
    have hξ : 0 ≤ gArg x g0 s ∧ gArg x g0 s ≤ 1 := by
      unfold gArg
      split_ifs <;> constructor <;> linarith [hat.1, hat.2]
    split_ifs with hlt
    · exact h42.1 ⟨hξ.1, hlt⟩
    · have heq : gArg x g0 s = 1 := le_antisymm hξ.2 (not_lt.1 hlt)
      rcases h42.2 heq with h0 | h1
      · exact h0
      · exfalso
        let σ : {a : Atom p n // 1 ≤ a.1.val} → Bool → Prop := fun g t => g = g0 ∧ t = s
        have hσ : ∀ i' < k.val + 1, ∀ g t, σ g t → jCost p n F i' (gy g t) = 0 := by
          rintro i' hi' g t ⟨rfl, rfl⟩
          match i', hi' with
          | 0, _ => rfl
          | 1, _ => simp [jCost, xFcoef]
          | i'' + 2, hi'' =>
            simp only [jCost, xFcoef, hg01, mul_zero, zero_add]
            split_ifs with hh hh2
            · omega
            · rfl
            · rfl
        have hfl := flipY_solSet σ (k.val + 1) hσ x (solSet_anti _ _ _ (by omega) hx)
        have hag : (jGame p n F).AgreeAbove (k.val + 1) x (flipY σ x) := by
          intro v hv
          apply flipY_ne
          rintro g t rfl
          exact absurd hv (by show ¬ (k.val + 1 < 1); omega)
        have hle := hx.2 (flipY σ x) hfl hag
        -- compute the criterion difference
        have hupd : flipY σ x = Function.update x (gy g0 s) 0 := by
          funext v
          cases v with
          | gy g t =>
            by_cases hgt : g = g0 ∧ t = s
            · obtain ⟨rfl, rfl⟩ := hgt
              simp only [flipY, Function.update_self]
              rw [if_pos ⟨⟨rfl, rfl⟩, heq⟩, h1]; ring
            · have hne : (gy g t : GVar p n F) ≠ gy g0 s := by
                intro hh; apply hgt; simpa using hh
              rw [Function.update_of_ne hne]
              simp only [flipY]
              rw [if_neg (fun hh => hgt hh.1)]
          | _ => rw [Function.update_of_ne (by simp)]; rfl
        have hcrit : (jGame p n F).crit (k.val + 1) (Function.update x (gy g0 s) 0) =
            (jGame p n F).crit (k.val + 1) x + jCost p n F (k.val + 1) (gy g0 s) * (0 - x (gy g0 s)) := by
          unfold MultilevelProgram.crit
          show ∑ v, jCost p n F (k.val+1) v * Function.update x (gy g0 s) 0 v = ∑ v, jCost p n F (k.val+1) v * x v + _
          have : ∀ v, jCost p n F (k.val+1) v * Function.update x (gy g0 s) 0 v =
              jCost p n F (k.val+1) v * x v +
                (if v = gy g0 s then jCost p n F (k.val+1) (gy g0 s) * (0 - x (gy g0 s)) else 0) := by
            intro v
            by_cases hv : v = gy g0 s
            · subst hv; simp
            · simp [hv]
          simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have hc2 : jCost p n F (k.val + 1) (gy g0 s) = 2 := by
          rw [hi]
          simp only [jCost]
          rw [if_pos (by omega)]
          simp [xFcoef, hg0, hi]
        rw [hupd, hcrit, hc2, h1] at hle
        linarith
  refine ⟨part1, ?_⟩
  rw [part1 false, part1 true]
  unfold gArg
  simp only [Bool.false_eq_true, if_false, if_true, hg01]
  obtain ⟨ha, hb⟩ := hat
  by_cases c1 : x (atom ⟨k, j⟩) < 1 <;> by_cases c2 : 1 - x (atom ⟨k, j⟩) < 1 <;>
    by_cases c3 : x (atom ⟨k, j⟩) = 0 ∨ x (atom ⟨k, j⟩) = 1 <;>
    simp only [c1, c2, c3, if_true, if_false] <;> norm_num
  all_goals (try rcases c3 with c3 | c3) <;> (try push Not at c1) <;> (try push Not at c2) <;>
    (try push Not at c3) <;> (try obtain ⟨c3, c4⟩ := c3) <;>
    first | linarith | (exfalso; apply c3; linarith) | (exfalso; apply c4; linarith)
