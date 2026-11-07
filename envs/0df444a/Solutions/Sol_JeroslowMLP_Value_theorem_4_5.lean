-- Prove2me | solution 1 for JeroslowMLP.Value.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:06:20.49003+00:00
-- url     : https://prove2.me/submissions/44552aae-8d1a-42e6-8fcf-02760be97147

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game
import Theorems.Thm_JeroslowMLP_Value_eq_4_2
import Theorems.Thm_JeroslowMLP_Value_eq_4_3
import Theorems.Thm_JeroslowMLP_Value_lemma_4_4

set_option autoImplicit false
open JeroslowMLP.Value MultilevelProgram GVar
open scoped Classical

namespace JMLC

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


/-! ### Criterion formulas and formula lemmas -/

lemma xFcoef_sum (x : GVar p n F → ℝ) : ∑ v, xFcoef v * x v = xF x := by
  cases F with
  | var a =>
    rw [Finset.sum_eq_single (atom a)]
    · simp [xFcoef, Formula.rootAtom, xF, Formula.nodeVal]
    · intro v _ hv
      cases v with
      | atom a' =>
        have : a ≠ a' := fun h => hv (by rw [h])
        simp [xFcoef, Formula.rootAtom, this]
      | node g => exact g.elim
      | _ => simp [xFcoef]
    · simp
  | neg G =>
    rw [Finset.sum_eq_single (GVar.node (F := .neg G) (show (Formula.neg G).Node from (none : Option G.Node)))]
    · simp [xFcoef, Formula.isRootNode, xF, Formula.nodeVal]
    · intro v _ hv
      cases v with
      | atom a' => simp [xFcoef, Formula.rootAtom]
      | node g =>
        cases g with
        | none => exact absurd rfl hv
        | some g => simp [xFcoef, Formula.isRootNode]
      | _ => simp [xFcoef]
    · simp
  | and G H =>
    rw [Finset.sum_eq_single (GVar.node (F := .and G H) (show (Formula.and G H).Node from (none : Option (G.Node ⊕ H.Node))))]
    · simp [xFcoef, Formula.isRootNode, xF, Formula.nodeVal]
    · intro v _ hv
      cases v with
      | atom a' => simp [xFcoef, Formula.rootAtom]
      | node g =>
        cases g with
        | none => exact absurd rfl hv
        | some g => simp [xFcoef, Formula.isRootNode]
      | _ => simp [xFcoef]
    · simp
  | or G H =>
    rw [Finset.sum_eq_single (GVar.node (F := .or G H) (show (Formula.or G H).Node from (none : Option (G.Node ⊕ H.Node))))]
    · simp [xFcoef, Formula.isRootNode, xF, Formula.nodeVal]
    · intro v _ hv
      cases v with
      | atom a' => simp [xFcoef, Formula.rootAtom]
      | node g =>
        cases g with
        | none => exact absurd rfl hv
        | some g => simp [xFcoef, Formula.isRootNode]
      | _ => simp [xFcoef]
    · simp

/-- Gadget-sum term of the criterion of the owner of block `b`. -/
lemma gy_sum (b : Fin p) (hb : 1 ≤ b.val) (x : GVar p n F → ℝ) :
    ∑ v : GVar p n F, (match v with
      | gy g _ => if g.1.1.val + 1 = b.val + 1 then (2 : ℝ) else 0
      | _ => 0) * x v =
    2 * ∑ j : Fin (n b), (x (gy ⟨⟨b, j⟩, hb⟩ false) + x (gy ⟨⟨b, j⟩, hb⟩ true)) := by
  have h1 : ∑ v : GVar p n F, (match v with
      | gy g _ => if g.1.1.val + 1 = b.val + 1 then (2 : ℝ) else 0
      | _ => 0) * x v =
      ∑ gs : {a : Atom p n // 1 ≤ a.1.val} × Bool,
        (if gs.1.1.1.val + 1 = b.val + 1 then (2 : ℝ) else 0) * x (gy gs.1 gs.2) := by
    symm
    apply Fintype.sum_of_injective (fun gs => (gy gs.1 gs.2 : GVar p n F))
    · rintro ⟨g, s⟩ ⟨g', s'⟩ h
      simp only [GVar.gy.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
    · intro v hv
      cases v with
      | gy g s => exact absurd ⟨(g, s), rfl⟩ hv
      | _ => simp
    · intro gs; rfl
  rw [h1, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_of_injective (fun j : Fin (n b) => (⟨⟨b, j⟩, hb⟩ : {a : Atom p n // 1 ≤ a.1.val}))
  · intro j j' h
    simp only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
    exact h
  · rintro ⟨⟨k', j'⟩, hg⟩ hv
    by_cases hk : k'.val = b.val
    · exfalso
      have hk' : k' = b := Fin.ext hk
      subst hk'
      exact hv ⟨j', rfl⟩
    · simp only
      rw [if_neg (by omega)]; ring
  · intro j
    simp
    ring

lemma crit_hi (b : Fin p) (hb : 1 ≤ b.val) (x : GVar p n F → ℝ) :
    (jGame p n F).crit (b.val + 1) x =
      (if Even (p - (b.val + 1)) then x one - xF x else xF x) +
      2 * ∑ j : Fin (n b), (x (gy ⟨⟨b, j⟩, hb⟩ false) + x (gy ⟨⟨b, j⟩, hb⟩ true)) := by
  obtain ⟨i, hi⟩ : ∃ i, b.val = i + 1 := ⟨b.val - 1, by omega⟩
  have hbp : i + 2 ≤ p := by have := b.isLt; omega
  rw [← gy_sum b hb x, ← xFcoef_sum x]
  unfold MultilevelProgram.crit
  show ∑ v, jCost p n F (b.val + 1) v * x v = _
  have key : ∀ v : GVar p n F, jCost p n F (b.val + 1) v * x v =
      (if Even (p - (b.val + 1)) then -1 else 1) * (xFcoef v * x v) +
      ((if v = one then (if Even (p - (b.val + 1)) then x one else 0) else 0) +
      (match v with
        | gy g _ => if g.1.1.val + 1 = b.val + 1 then (2 : ℝ) else 0
        | _ => 0) * x v) := by
    intro v
    rw [hi]
    simp only [jCost]
    rw [if_pos hbp]
    cases v with
    | one => simp; split_ifs <;> ring
    | gy g s => simp [xFcoef]
    | _ => simp
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  split_ifs <;> ring

/-- On binary atoms, `L_G` forces binary node values. -/
lemma lsys_binary {α : Type} : ∀ (G : Formula α) (xa : α → ℝ) (xn : G.Node → ℝ),
    (∀ a, IsBinary (xa a)) → G.LSys xa xn → (∀ g, IsBinary (xn g)) ∧ IsBinary (G.nodeVal xa xn)
  | .var a, xa, xn, ha, _ => ⟨fun g => g.elim, ha a⟩
  | .neg G, xa, xn, ha, ⟨h1, h2, h3, h4⟩ => by
    obtain ⟨ih1, ih2⟩ := lsys_binary G xa _ ha h1
    have hr : IsBinary (xn none) := by
      rw [h2]; rcases ih2 with h | h <;> rw [h] <;> norm_num [IsBinary]
    refine ⟨?_, hr⟩
    intro g; cases g with
    | none => exact hr
    | some g => exact ih1 g
  | .and G H, xa, xn, ha, ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
    obtain ⟨ihG1, ihG2⟩ := lsys_binary G xa _ ha h1
    obtain ⟨ihH1, ihH2⟩ := lsys_binary H xa _ ha h2
    have hr : IsBinary (xn none) := by
      unfold IsBinary at *
      rcases ihG2 with e1 | e1 <;> rcases ihH2 with e2 | e2 <;> rw [e1] at h3 h5 <;>
        rw [e2] at h4 h5 <;> first | (left; linarith) | (right; linarith)
    refine ⟨?_, hr⟩
    intro g; rcases g with _ | g | g
    · exact hr
    · exact ihG1 g
    · exact ihH1 g
  | .or G H, xa, xn, ha, ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
    obtain ⟨ihG1, ihG2⟩ := lsys_binary G xa _ ha h1
    obtain ⟨ihH1, ihH2⟩ := lsys_binary H xa _ ha h2
    have hr : IsBinary (xn none) := by
      unfold IsBinary at *
      rcases ihG2 with e1 | e1 <;> rcases ihH2 with e2 | e2 <;> rw [e1] at h3 h4 <;>
        rw [e2] at h3 h5 <;> first | (left; linarith) | (right; linarith)
    refine ⟨?_, hr⟩
    intro g; rcases g with _ | g | g
    · exact hr
    · exact ihG1 g
    · exact ihH1 g

/-- `L_G` keeps `x(G)` in `[0,1]`. -/
lemma lsys_bounds {α : Type} : ∀ (G : Formula α) (xa : α → ℝ) (xn : G.Node → ℝ),
    (∀ a, 0 ≤ xa a ∧ xa a ≤ 1) → G.LSys xa xn → 0 ≤ G.nodeVal xa xn ∧ G.nodeVal xa xn ≤ 1
  | .var a, _, _, ha, _ => ha a
  | .neg _, _, _, _, ⟨_, _, h3, h4⟩ => ⟨h3, h4⟩
  | .and _ _, _, _, _, ⟨_, _, _, _, _, h6, h7⟩ => ⟨h6, h7⟩
  | .or _ _, _, _, _, ⟨_, _, _, _, _, h6, h7⟩ => ⟨h6, h7⟩

lemma qholds_congr (k : ℕ) : ∀ (α α' : Atom p n → Bool),
    (∀ a : Atom p n, k ≤ a.1.val → α a = α' a) → (QHolds p n F k α ↔ QHolds p n F k α') := by
  induction k with
  | zero =>
    intro α α' h
    have : α = α' := funext fun a => h a (Nat.zero_le _)
    rw [this]
  | succ k ih =>
    intro α α' h
    unfold QHolds
    by_cases hk : k < p
    · have hb : ∀ β, (QHolds p n F k (setBlock α ⟨k, hk⟩ β) ↔
          QHolds p n F k (setBlock α' ⟨k, hk⟩ β)) := by
        intro β
        apply ih
        intro a ha
        unfold setBlock
        split_ifs with h1
        · rfl
        · apply h
          have : a.1.val ≠ k := fun h2 => h1 (Fin.ext h2)
          omega
      simp only [dif_pos hk]
      split_ifs
      · exact exists_congr hb
      · exact forall_congr' hb
    · simp only [dif_neg hk]
      apply ih
      intro a ha
      exfalso; have := a.1.isLt; omega

end JMLC


open JMLC

theorem solution (p : ℕ) (hp : 2 ≤ p) (n : Fin p → ℕ) (F : Formula (Atom p n)) :
    let S := (jGame p n F).solSet (p + 1)
    let top : Fin p := ⟨p - 1, by omega⟩
    S.Nonempty ∧
    (∀ x ∈ S, (∀ a, IsBinary (x (atom a))) ∧ (∀ g, IsBinary (x (node g)))) ∧
    (∀ x ∈ S, (xF x = 1 ↔ Sentence33 p n F)) ∧
    (Sentence33 p n F → (jGame p n F).HasValue (p + 1) (2 * (n top : ℝ))) ∧
    (¬ Sentence33 p n F → (jGame p n F).HasValue (p + 1) (2 * (n top : ℝ) + 1)) ∧
    (Sentence33 p n F → ∀ w : Fin (n top) → ℝ,
      ((∃ x ∈ S, ∀ j, x (atom ⟨top, j⟩) = w j) ↔
        ((∀ j, IsBinary (w j)) ∧
          QHolds p n F (p - 1) (fun a => if h : a.1 = top then
            decide (w (Fin.cast (by rw [h]) a.2) = 1) else false)))) := by
  intro S top
  have htop1 : 1 ≤ top.val := by show 1 ≤ p - 1; omega
  have htopv : top.val + 1 = p := by show p - 1 + 1 = p; omega
  have hL := JeroslowMLP.Value.lemma_4_4 p n F p (by omega) le_rfl (fun _ => false)
  have hLp := JeroslowMLP.Value.lemma_4_4 p n F (p - 1) (by omega) (by omega)
  have hS : ∀ x ∈ S, x ∈ (jGame p n F).solSet (p + 1) ∧
      ∀ a : Atom p n, p ≤ a.1.val → x (atom a) = if (fun _ => false) a then 1 else 0 :=
    fun x hx => ⟨hx, fun a ha => absurd ha (by have := a.1.isLt; omega)⟩
  have item1 : S.Nonempty := by
    obtain ⟨x, hx⟩ := hL.1
    exact ⟨x, hx.1⟩
  have item2 : ∀ x ∈ S, (∀ a, IsBinary (x (atom a))) ∧ (∀ g, IsBinary (x (node g))) :=
    fun x hx => ⟨(hL.2 x (hS x hx)).1, (hL.2 x (hS x hx)).2.1⟩
  have item3 : ∀ x ∈ S, (xF x = 1 ↔ Sentence33 p n F) :=
    fun x hx => (hL.2 x (hS x hx)).2.2
  have hfeasS : ∀ x ∈ S, x ∈ jFeasible p n F := fun x hx => solSet_anti _ 0 _ (by omega) hx
  -- binary x(F)
  have hxFbin : ∀ x ∈ S, IsBinary (xF x) := by
    intro x hx
    exact (lsys_binary F _ _ (item2 x hx).1 (hfeasS x hx).2.1).2
  -- criterion of player p on S
  have hcritS : ∀ x ∈ S, (jGame p n F).crit p x = 1 - xF x + 2 * (n top : ℝ) := by
    intro x hx
    have hc := crit_hi top htop1 x
    rw [htopv] at hc
    rw [hc, if_pos (by simp), (hfeasS x hx).2.2.1]
    have hx' : x ∈ (jGame p n F).solSet (top.val + 2) := by
      rw [show top.val + 2 = p + 1 by omega]; exact hx
    have hsum : ∀ j : Fin (n top), x (gy ⟨⟨top, j⟩, htop1⟩ false) + x (gy ⟨⟨top, j⟩, htop1⟩ true) = 1 := by
      intro j
      rw [(JeroslowMLP.Value.eq_4_3 p n F top htop1 x hx' j).2, if_pos (show _ ∨ _ from (item2 x hx).1 ⟨top, j⟩)]
    simp only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hval : ∀ val : ℝ, (∀ x ∈ S, 1 - xF x + 2 * (n top : ℝ) = val) →
      (jGame p n F).HasValue (p + 1) val := by
    intro val h
    refine ⟨by omega, item1, fun x hx => ?_⟩
    show (jGame p n F).crit (p + 1 - 1) x = val
    rw [show p + 1 - 1 = p by omega, hcritS x hx, h x hx]
  refine ⟨item1, item2, item3, ?_, ?_, ?_⟩
  · intro hs
    apply hval
    intro x hx
    rw [(item3 x hx).2 hs]; ring
  · intro hs
    apply hval
    intro x hx
    have : xF x = 0 := by
      rcases hxFbin x hx with h | h
      · exact h
      · exact absurd ((item3 x hx).1 h) hs
    rw [this]; ring
  · intro hs w
    -- the truth assignment attached to `w`
    set αw : Atom p n → Bool := fun a => if h : a.1 = top then
      decide (w (Fin.cast (by rw [h]) a.2) = 1) else false with hαw
    have hαw_top : ∀ j, αw ⟨top, j⟩ = decide (w j = 1) := by
      intro j; simp [hαw]
    constructor
    · rintro ⟨x, hx, hw⟩
      have hwb : ∀ j, IsBinary (w j) := fun j => hw j ▸ (item2 x hx).1 ⟨top, j⟩
      refine ⟨hwb, ?_⟩
      set v : Atom p n → Bool := fun a => decide (x (atom a) = 1) with hv
      have hxp : x ∈ (jGame p n F).solSet (p - 1 + 1) :=
        solSet_anti _ _ _ (by omega) hx
      have hslice : x ∈ (jGame p n F).solSet (p - 1 + 1) ∧
          ∀ a : Atom p n, p - 1 ≤ a.1.val → x (atom a) = if v a then 1 else 0 := by
        refine ⟨hxp, fun a _ => ?_⟩
        rcases (item2 x hx).1 a with h | h <;> simp [hv, h]
      have hq := ((hLp v).2 x hslice).2.2.1 ((item3 x hx).2 hs)
      refine (qholds_congr (p - 1) v αw ?_).1 hq
      rintro ⟨k', j'⟩ hk'
      have hk : k' = top := Fin.ext (by show k'.val = p - 1; have := k'.isLt; simp at hk'; omega)
      subst hk
      rw [hαw_top, hv]
      simp only
      rw [hw j']
    · rintro ⟨hwb, hq⟩
      obtain ⟨x, hxsl, hxat⟩ := (hLp αw).1
      have hxat' : ∀ j, x (atom ⟨top, j⟩) = w j := by
        intro j
        rw [hxat ⟨top, j⟩ (by show p - 1 ≤ p - 1; exact le_rfl), hαw_top]
        rcases hwb j with h | h <;> simp [h]
      have hxF1 : xF x = 1 := ((hLp αw).2 x ⟨hxsl, hxat⟩).2.2.2 hq
      -- flip the redundant `y = 1` of the top block
      let σ : {a : Atom p n // 1 ≤ a.1.val} → Bool → Prop :=
        fun g s => g.1.1 = top ∧ x (gy g s) = 1
      have hσ : ∀ i < p, ∀ g s, σ g s → jCost p n F i (gy g s) = 0 := by
        rintro i hi g s ⟨hg, -⟩
        match i, hi with
        | 0, _ => rfl
        | 1, _ => simp [jCost, xFcoef]
        | i'' + 2, hi'' =>
          have : g.1.1.val + 1 ≠ i'' + 2 := by rw [hg]; show p - 1 + 1 ≠ i'' + 2; omega
          simp only [jCost, xFcoef, mul_zero, zero_add]
          split_ifs <;> rfl
      have hxp : x ∈ (jGame p n F).solSet p := by
        have : p - 1 + 1 = p := by omega
        rw [this] at hxsl; exact hxsl
      set x'' := flipY σ x with hx''
      have hx''p : x'' ∈ (jGame p n F).solSet p := flipY_solSet σ p hσ x hxp
      have hx''2 : x'' ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ hp hx''p
      have hx2 : x ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ hp hxp
      have hfe : x ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hxp
      -- the y's of x'' on the top block
      have hy'' : ∀ j, x'' (gy ⟨⟨top, j⟩, htop1⟩ false) + x'' (gy ⟨⟨top, j⟩, htop1⟩ true) = 1 := by
        intro j
        have hyv : ∀ s, (gArg x ⟨⟨top, j⟩, htop1⟩ s < 1 → x'' (gy ⟨⟨top, j⟩, htop1⟩ s) = 1) ∧
            (gArg x ⟨⟨top, j⟩, htop1⟩ s = 1 → x'' (gy ⟨⟨top, j⟩, htop1⟩ s) = 0) := by
          intro s
          have hξ : 0 ≤ gArg x ⟨⟨top, j⟩, htop1⟩ s := by
            unfold gArg; have := hfe.1 ⟨top, j⟩; split_ifs <;> linarith [this.1, this.2]
          constructor
          · intro hlt
            have := (JeroslowMLP.Value.eq_4_2 p n F x'' hx''2 ⟨⟨top, j⟩, htop1⟩ s).1
            rw [flipY_gArg] at this
            exact this ⟨hξ, hlt⟩
          · intro h1
            rcases (JeroslowMLP.Value.eq_4_2 p n F x hx2 ⟨⟨top, j⟩, htop1⟩ s).2 h1 with h0 | h1'
            · show flipY σ x (gy _ s) = 0
              simp only [flipY]
              rw [if_neg (fun hh => by have h5 : x (gy _ s) = 1 := hh.1.2; rw [h0] at h5; norm_num at h5)]
              exact h0
            · show flipY σ x (gy _ s) = 0
              simp only [flipY]
              rw [if_pos ⟨⟨rfl, h1'⟩, h1⟩, h1']; ring
        have hwj := hwb j
        rw [← hxat' j] at hwj
        unfold gArg at hyv
        simp only [Bool.false_eq_true, if_false, if_true] at hyv
        rcases hwj with h | h
        · rw [(hyv false).1 (by rw [h]; norm_num), (hyv true).2 (by rw [h]; norm_num)]; ring
        · rw [(hyv false).2 h, (hyv true).1 (by rw [h]; norm_num)]; ring
      have hcrit'' : (jGame p n F).crit p x'' = 2 * (n top : ℝ) := by
        have hc := crit_hi top htop1 x''
        rw [htopv] at hc
        rw [hc, if_pos (by simp), hx'', flipY_xF, hxF1]
        rw [show flipY σ x one = x one from rfl, hfe.2.2.1]
        rw [← hx'']
        simp only [hy'', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        ring
      -- lower bound for every competitor
      have hlow : ∀ x' ∈ (jGame p n F).solSet p, 2 * (n top : ℝ) ≤ (jGame p n F).crit p x' := by
        intro x' hx'
        have hx'2 : x' ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ hp hx'
        have hfe' : x' ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hx'
        have hc := crit_hi top htop1 x'
        rw [htopv] at hc
        rw [hc, if_pos (by simp), hfe'.2.2.1]
        have hb := lsys_bounds F _ _ hfe'.1 hfe'.2.1
        have hxFle : xF x' ≤ 1 := hb.2
        have hj : ∀ j : Fin (n top), (1 : ℝ) ≤ x' (gy ⟨⟨top, j⟩, htop1⟩ false) + x' (gy ⟨⟨top, j⟩, htop1⟩ true) := by
          intro j
          have ha := hfe'.1 ⟨top, j⟩
          have hyf := (hfe'.2.2.2.1 ⟨⟨top, j⟩, htop1⟩ false).2.2
          have hyt := (hfe'.2.2.2.1 ⟨⟨top, j⟩, htop1⟩ true).2.2
          have e1 := (JeroslowMLP.Value.eq_4_2 p n F x' hx'2 ⟨⟨top, j⟩, htop1⟩ false).1
          have e2 := (JeroslowMLP.Value.eq_4_2 p n F x' hx'2 ⟨⟨top, j⟩, htop1⟩ true).1
          unfold gArg at e1 e2
          simp only [Bool.false_eq_true, if_false, if_true] at e1 e2
          by_cases hlt : x' (atom ⟨top, j⟩) < 1
          · rw [e1 ⟨ha.1, hlt⟩]; linarith [hyt.1]
          · rw [e2 ⟨by linarith [ha.2], by linarith⟩]; linarith [hyf.1]
        have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
        linarith
      refine ⟨x'', ⟨hx''p, fun x' hx' _ => ?_⟩, fun j => ?_⟩
      · rw [hcrit'']; exact hlow x' hx'
      · show flipY σ x (atom _) = w j
        exact hxat' j
