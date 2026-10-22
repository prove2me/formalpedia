-- Prove2me | solution 1 for JeroslowMLP.Value.eq_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:15:03.46034+00:00
-- url     : https://prove2.me/submissions/ab83dcab-89ea-4ecf-8898-ae8c3d6f7509

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

lemma JML_crit_upd (i : ℕ) (x : GVar p n F → ℝ) (v0 : GVar p n F) (t : ℝ) :
    (jGame p n F).crit i (Function.update x v0 t) =
      (jGame p n F).crit i x + jCost p n F i v0 * (t - x v0) := by
  unfold MultilevelProgram.crit
  show ∑ v, jCost p n F i v * Function.update x v0 t v = ∑ v, jCost p n F i v * x v + _
  have : ∀ v, jCost p n F i v * Function.update x v0 t v =
      jCost p n F i v * x v + (if v = v0 then jCost p n F i v0 * (t - x v0) else 0) := by
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
  rw [JML_crit_upd 0] at this
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


theorem JML_bookkeeper (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n))
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


lemma JML_dbl_eval (x : GVar p n F → ℝ) (g0 : {a : Atom p n // 1 ≤ a.1.val}) (s0 : Bool) (y t : ℝ) :
    (∀ a, Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t (atom a) = x (atom a)) ∧
    (∀ g, Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t (node g) = x (node g)) ∧
    Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t one = x one ∧
    (∀ a, Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t (fz a) = x (fz a)) ∧
    Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t fzF = x fzF ∧
    Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t (gy g0 s0) = y ∧
    Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t (gz g0 s0) = t ∧
    (∀ v, v ≠ gy g0 s0 → v ≠ gz g0 s0 →
      Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t v = x v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  · intro a; rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  · intro a; rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp)]
  · rw [Function.update_of_ne (by simp), Function.update_self]
  · rw [Function.update_self]
  · intro v h1 h2
    rw [Function.update_of_ne h2, Function.update_of_ne h1]

lemma JML_dbl_feas (x : GVar p n F → ℝ) (hx : x ∈ jFeasible p n F)
    (g0 : {a : Atom p n // 1 ≤ a.1.val}) (s0 : Bool) (y t : ℝ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (h1 : 2 * y - gArg x g0 s0 ≤ t) (h2 : -(2 * y - gArg x g0 s0) ≤ t) :
    Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t ∈ jFeasible p n F := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hx
  obtain ⟨ea, en, eo, efz, efF, egy, egz, eoth⟩ := JML_dbl_eval x g0 s0 y t
  set X := Function.update (Function.update x (gy g0 s0) y) (gz g0 s0) t with hX
  have hga : ∀ g s, gArg X g s = gArg x g s := by
    intro g s; unfold gArg; rw [ea]
  have hxF : xF X = xF x := by
    unfold xF
    have e1 : (fun a => X (atom a)) = fun a => x (atom a) := funext ea
    have e2 : (fun g => X (node g)) = fun g => x (node g) := funext en
    rw [e1, e2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a; rw [ea]; exact c1 a
  · have e1 : (fun a => X (atom a)) = fun a => x (atom a) := funext ea
    have e2 : (fun g => X (node g)) = fun g => x (node g) := funext en
    rw [e1, e2]; exact c2
  · rw [eo]; exact c3
  · intro g s
    rw [hga]
    by_cases h : g = g0 ∧ s = s0
    · obtain ⟨rfl, rfl⟩ := h
      rw [egy, egz]
      exact ⟨h1, h2, hy0, hy1⟩
    · have hne1 : (gy g s : GVar p n F) ≠ gy g0 s0 := by
        intro hh; apply h; simpa using hh
      have hne2 : (gz g s : GVar p n F) ≠ gz g0 s0 := by
        intro hh; apply h; simpa using hh
      rw [eoth _ hne1 (by simp), eoth _ (by simp) hne2]
      exact c4 g s
  · intro a
    rw [efz, ea]; exact c5 a
  · rw [efF, hxF]; exact c6

theorem solution (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n))
    (x : GVar p n F → ℝ) (hx : x ∈ (jGame p n F).solSet 2)
    (g : {a : Atom p n // 1 ≤ a.1.val}) (s : Bool) :
    (0 ≤ gArg x g s ∧ gArg x g s < 1 → x (gy g s) = 1) ∧
    (gArg x g s = 1 → x (gy g s) = 0 ∨ x (gy g s) = 1) := by
  have hx1 : x ∈ (jGame p n F).solSet 1 := hx.1
  have hfeas : x ∈ jFeasible p n F := hx1.1
  have hz := (JML_bookkeeper p n F x hx1).1 g s
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hfeas
  have hξ : 0 ≤ gArg x g s ∧ gArg x g s ≤ 1 := by
    unfold gArg
    have := c1 g.1
    split_ifs <;> constructor <;> linarith [this.1, this.2]
  obtain ⟨hc1, hc2, hy0, hy1⟩ := c4 g s
  set ξ := gArg x g s with hξdef
  set y0 := x (gy g s) with hy0def
  set z0 := x (gz g s) with hz0def
  -- key inequality: the bookkeeper's gadget value is at least 2 - ξ
  have key : 2 - ξ ≤ z0 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨ea, en, eo, efz, efF, egy, egz, eoth⟩ := JML_dbl_eval x g s 1 (2 - ξ)
    set x' := Function.update (Function.update x (gy g s) 1) (gz g s) (2 - ξ) with hx'
    have hx'feas : x' ∈ jFeasible p n F :=
      JML_dbl_feas x ⟨c1, c2, c3, c4, c5, c6⟩ g s 1 (2 - ξ) (by norm_num) le_rfl (by linarith)
        (by linarith [hξ.2])
    -- x' is in S_1
    have hx'S1 : x' ∈ (jGame p n F).solSet 1 := by
      refine ⟨hx'feas, ?_⟩
      intro x'' hx'' hag
      have hag' : ∀ v, 0 < jOwner v → x'' v = x' v := hag
      have hga'' : gArg x'' g s = ξ := by
        rw [hξdef]
        unfold gArg
        rw [hag' (atom g.1) (by show 0 < g.1.1.val + 1; omega), ea]
      have hgy'' : x'' (gy g s) = 1 := by
        rw [hag' (gy g s) (by show 0 < 1; norm_num), egy]
      obtain ⟨-, -, -, d4, -⟩ := id hx''
      have hz'' : 2 - ξ ≤ x'' (gz g s) := by
        have := (d4 g s).1
        rw [hga'', hgy''] at this
        linarith
      -- the competitor for x
      obtain ⟨ea3, en3, eo3, efz3, efF3, egy3, egz3, eoth3⟩ := JML_dbl_eval x'' g s y0 z0
      set x3 := Function.update (Function.update x'' (gy g s) y0) (gz g s) z0 with hx3
      have hx3feas : x3 ∈ jFeasible p n F := by
        apply JML_dbl_feas x'' hx'' g s y0 z0 hy0 hy1
        · rw [hga'']; exact hc1
        · rw [hga'']; exact hc2
      have hag3 : (jGame p n F).AgreeAbove 0 x x3 := by
        intro v hv
        by_cases h1 : v = gy g s
        · subst h1; rw [egy3]
        · by_cases h2 : v = gz g s
          · subst h2; exact absurd hv (by show ¬ 0 < jOwner (gz g s : GVar p n F); simp [jOwner])
          · rw [eoth3 v h1 h2, hag' v hv, eoth v h1 h2]
      have hle := hx1.2 x3 hx3feas hag3
      -- crit computations
      have hc3 : (jGame p n F).crit 0 x3 = (jGame p n F).crit 0 x'' + (z0 - x'' (gz g s)) := by
        rw [hx3, JML_crit_upd 0, JML_crit_upd 0]
        have e1 : jCost p n F 0 (gz g s) = 1 := rfl
        have e2 : jCost p n F 0 (gy g s) = 0 := rfl
        rw [e1, e2, Function.update_of_ne (by simp)]
        ring
      have hc' : (jGame p n F).crit 0 x' = (jGame p n F).crit 0 x + ((2 - ξ) - z0) := by
        rw [hx', JML_crit_upd 0, JML_crit_upd 0]
        have e1 : jCost p n F 0 (gz g s) = 1 := rfl
        have e2 : jCost p n F 0 (gy g s) = 0 := rfl
        rw [e1, e2, Function.update_of_ne (by simp)]
        ring
      linarith
    have hag1 : (jGame p n F).AgreeAbove 1 x x' := by
      intro v hv
      have h1 : v ≠ gy g s := by
        intro h; subst h; exact absurd hv (by show ¬ 1 < jOwner (gy g s : GVar p n F); simp [jOwner])
      have h2 : v ≠ gz g s := by
        intro h; subst h; exact absurd hv (by show ¬ 1 < jOwner (gz g s : GVar p n F); simp [jOwner])
      exact eoth v h1 h2
    have hle := hx.2 x' hx'S1 hag1
    have hc' : (jGame p n F).crit 1 x' = (jGame p n F).crit 1 x - ((2 - ξ) - z0) := by
      rw [hx', JML_crit_upd 1, JML_crit_upd 1]
      have e1 : jCost p n F 1 (gz g s) = -1 := by simp [jCost, xFcoef]
      have e2 : jCost p n F 1 (gy g s) = 0 := by simp [jCost, xFcoef]
      rw [e1, e2, Function.update_of_ne (by simp)]
      ring
    linarith
  have hzabs : z0 = |2 * y0 - ξ| := hz
  constructor
  · rintro ⟨-, hlt⟩
    have : 2 - ξ ≤ |2 * y0 - ξ| := hzabs ▸ key
    rcases le_abs'.1 this with h | h
    · linarith
    · linarith
  · intro h1
    have : 2 - ξ ≤ |2 * y0 - ξ| := hzabs ▸ key
    rw [h1] at this
    rcases le_abs'.1 this with h | h
    · left; linarith
    · right; linarith

end
