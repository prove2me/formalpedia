-- Prove2me | solution 1 for JeroslowMLP.Value.bookkeeper_in_S1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:05:20.141497+00:00
-- url     : https://prove2.me/submissions/bf3bd6eb-2314-4314-953e-ba537bf01654

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game

set_option autoImplicit false
open JeroslowMLP.Value MultilevelProgram GVar
open scoped Classical

section
variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

lemma JML_gArg_upd (x : GVar p n F → ℝ) (v0 : GVar p n F) (t : ℝ)
    (h : ∀ a, GVar.atom a ≠ v0) (g : {a : Atom p n // 1 ≤ a.1.val}) (s : Bool) :
    gArg (Function.update x v0 t) g s = gArg x g s := by
  unfold gArg
  rw [Function.update_of_ne (h g.1)]

lemma JML_xF_upd (x : GVar p n F → ℝ) (v0 : GVar p n F) (t : ℝ)
    (h1 : ∀ a, GVar.atom a ≠ v0) (h2 : ∀ g, GVar.node g ≠ v0) :
    xF (Function.update x v0 t) = xF x := by
  unfold xF
  have e1 : (fun a => Function.update x v0 t (atom a)) = fun a => x (atom a) := by
    funext a; exact Function.update_of_ne (h1 a) _ _
  have e2 : (fun g => Function.update x v0 t (node g)) = fun g => x (node g) := by
    funext g; exact Function.update_of_ne (h2 g) _ _
  rw [e1, e2]

lemma JML_crit_upd (x : GVar p n F → ℝ) (v0 : GVar p n F) (t : ℝ) :
    (jGame p n F).crit 0 (Function.update x v0 t) =
      (jGame p n F).crit 0 x + jCost p n F 0 v0 * (t - x v0) := by
  unfold MultilevelProgram.crit
  show ∑ v, jCost p n F 0 v * Function.update x v0 t v = ∑ v, jCost p n F 0 v * x v + _
  have : ∀ v, jCost p n F 0 v * Function.update x v0 t v =
      jCost p n F 0 v * x v + (if v = v0 then jCost p n F 0 v0 * (t - x v0) else 0) := by
    intro v
    by_cases hv : v = v0
    · subst hv; simp; ring
    · simp [Function.update_of_ne hv, hv]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma JML_bk (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet 1) (v0 : GVar p n F)
    (hown : jOwner v0 = 0) (t : ℝ) (hfeas : Function.update x v0 t ∈ jFeasible p n F) :
    0 ≤ jCost p n F 0 v0 * (t - x v0) := by
  obtain ⟨-, hmin⟩ := hx
  have := hmin (Function.update x v0 t) hfeas (by
    intro v hv
    by_cases h : v = v0
    · subst h
      exact absurd hv (by show ¬ 0 < jOwner v; rw [hown]; exact lt_irrefl 0)
    · exact Function.update_of_ne h _ _)
  rw [JML_crit_upd] at this
  linarith

lemma JML_upd_base (x : GVar p n F → ℝ) (hx : x ∈ jFeasible p n F) (v0 : GVar p n F) (t : ℝ)
    (h1 : ∀ a, GVar.atom a ≠ v0) (h2 : ∀ g, GVar.node g ≠ v0) (h3 : GVar.one ≠ v0) :
    (∀ a, 0 ≤ Function.update x v0 t (atom a) ∧ Function.update x v0 t (atom a) ≤ 1) ∧
    F.LSys (fun a => Function.update x v0 t (atom a)) (fun g => Function.update x v0 t (node g)) ∧
    Function.update x v0 t one = 1 := by
  obtain ⟨c1, c2, c3, -⟩ := hx
  have e1 : (fun a => Function.update x v0 t (atom a)) = fun a => x (atom a) := by
    funext a; exact Function.update_of_ne (h1 a) _ _
  have e2 : (fun g => Function.update x v0 t (node g)) = fun g => x (node g) := by
    funext g; exact Function.update_of_ne (h2 g) _ _
  refine ⟨?_, ?_, ?_⟩
  · intro a; rw [Function.update_of_ne (h1 a)]; exact c1 a
  · rw [e1, e2]; exact c2
  · rw [Function.update_of_ne h3]; exact c3

theorem solution (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n))
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet 1) :
    (∀ g s, x (gz g s) = |2 * x (gy g s) - gArg x g s|) ∧
    (∀ a, x (fz a) = min (x (atom a.1)) (1 - x (atom a.1))) ∧
    x fzF = min (xF x) (1 - xF x) := by
  have hfeas : x ∈ jFeasible p n F := hx.1
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hfeas
  refine ⟨?_, ?_, ?_⟩
  · -- the gadget variables z
    intro g0 s0
    set t := |2 * x (gy g0 s0) - gArg x g0 s0| with ht
    have hfe : Function.update x (gz g0 s0) t ∈ jFeasible p n F := by
      have hb := JML_upd_base x ⟨c1, c2, c3, c4, c5, c6⟩ (gz g0 s0) t (by simp) (by simp) (by simp)
      refine ⟨hb.1, hb.2.1, hb.2.2, ?_, ?_, ?_⟩
      · intro g s
        rw [JML_gArg_upd x (gz g0 s0) t (by simp), Function.update_of_ne (by simp : gy g s ≠ gz g0 s0)]
        by_cases h : g = g0 ∧ s = s0
        · obtain ⟨rfl, rfl⟩ := h
          rw [Function.update_self]
          obtain ⟨_, _, h3, h4⟩ := c4 g s
          exact ⟨le_abs_self _, neg_le_abs _, h3, h4⟩
        · rw [Function.update_of_ne (by simpa using h)]
          exact c4 g s
      · intro a
        rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
        exact c5 a
      · rw [JML_xF_upd x (gz g0 s0) t (by simp) (by simp), Function.update_of_ne (by simp)]
        exact c6
    have hbk := JML_bk x hx (gz g0 s0) rfl t hfe
    have hcost : jCost p n F 0 (gz g0 s0) = 1 := rfl
    rw [hcost] at hbk
    obtain ⟨h1, h2, -⟩ := c4 g0 s0
    apply le_antisymm
    · linarith
    · rw [ht]; apply abs_le.2; constructor <;> linarith
  · -- the (4.6) variables on block X_1
    intro a0
    set t := min (x (atom a0.1)) (1 - x (atom a0.1)) with ht
    have hfe : Function.update x (fz a0) t ∈ jFeasible p n F := by
      have hb := JML_upd_base x ⟨c1, c2, c3, c4, c5, c6⟩ (fz a0) t (by simp) (by simp) (by simp)
      refine ⟨hb.1, hb.2.1, hb.2.2, ?_, ?_, ?_⟩
      · intro g s
        rw [JML_gArg_upd x (fz a0) t (by simp), Function.update_of_ne (by simp : gy g s ≠ fz a0),
          Function.update_of_ne (by simp : gz g s ≠ fz a0)]
        exact c4 g s
      · intro a
        rw [Function.update_of_ne (by simp : atom a.1 ≠ fz a0)]
        by_cases h : a = a0
        · subst h
          rw [Function.update_self]
          exact ⟨min_le_left _ _, min_le_right _ _⟩
        · rw [Function.update_of_ne (by simpa using h)]
          exact c5 a
      · rw [JML_xF_upd x (fz a0) t (by simp) (by simp), Function.update_of_ne (by simp)]
        exact c6
    have hbk := JML_bk x hx (fz a0) rfl t hfe
    have hcost : jCost p n F 0 (fz a0) = -1 := rfl
    rw [hcost] at hbk
    obtain ⟨h1, h2⟩ := c5 a0
    apply le_antisymm
    · exact le_min h1 h2
    · rw [ht]; linarith
  · -- the (4.6) variable on x(F)
    set t := min (xF x) (1 - xF x) with ht
    have hfe : Function.update x fzF t ∈ jFeasible p n F := by
      have hb := JML_upd_base x ⟨c1, c2, c3, c4, c5, c6⟩ fzF t (by simp) (by simp) (by simp)
      refine ⟨hb.1, hb.2.1, hb.2.2, ?_, ?_, ?_⟩
      · intro g s
        rw [JML_gArg_upd x fzF t (by simp), Function.update_of_ne (by simp : gy g s ≠ fzF),
          Function.update_of_ne (by simp : gz g s ≠ fzF)]
        exact c4 g s
      · intro a
        rw [Function.update_of_ne (by simp : atom a.1 ≠ fzF), Function.update_of_ne (by simp : fz a ≠ fzF)]
        exact c5 a
      · rw [JML_xF_upd x fzF t (by simp) (by simp), Function.update_self]
        exact ⟨min_le_left _ _, min_le_right _ _⟩
    have hbk := JML_bk x hx fzF rfl t hfe
    have hcost : jCost p n F 0 fzF = -1 := rfl
    rw [hcost] at hbk
    obtain ⟨h1, h2⟩ := c6
    apply le_antisymm
    · exact le_min h1 h2
    · rw [ht]; linarith

end
