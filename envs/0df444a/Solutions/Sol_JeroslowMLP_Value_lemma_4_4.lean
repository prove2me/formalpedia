-- Prove2me | solution 1 for JeroslowMLP.Value.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:14:45.65818+00:00
-- url     : https://prove2.me/submissions/2b1d96a1-8cd7-4214-a2ce-e06822ccfbc3

import Mathlib
import Definitions.Def_JeroslowMLP_Value_Game
import Theorems.Thm_JeroslowMLP_Value_eq_4_2
import Theorems.Thm_JeroslowMLP_Value_bookkeeper_in_S1
import Theorems.Thm_JeroslowMLP_Value_lemma_3_1
import Theorems.Thm_JeroslowMLP_Value_lemma_4_1

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


namespace JML44

open JMLC

variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

noncomputable def Wn (F : Formula (Atom p n)) (α : Atom p n → Bool) : F.Node → ℝ :=
  Classical.choose (JeroslowMLP.Value.lemma_3_1 p n F α).1.exists

lemma Wn_spec (α : Atom p n → Bool) :
    (∀ g, IsBinary (Wn F α g)) ∧ F.LSys (fun a => if α a then 1 else 0) (Wn F α) :=
  Classical.choose_spec (JeroslowMLP.Value.lemma_3_1 p n F α).1.exists

/-- The explicit bookkeeper response to binary atoms `α` and gadget values `yv`. -/
noncomputable def mkPt (F : Formula (Atom p n)) (α : Atom p n → Bool)
    (yv : {a : Atom p n // 1 ≤ a.1.val} → Bool → ℝ) : GVar p n F → ℝ
  | atom a => if α a then 1 else 0
  | node g => Wn F α g
  | one => 1
  | gy g s => yv g s
  | gz g s => |2 * yv g s - (if s then 1 - (if α g.1 then 1 else 0) else (if α g.1 then 1 else 0))|
  | fz _ => 0
  | fzF => 0

lemma bin_bv (b : Bool) : IsBinary (if b then (1 : ℝ) else 0) := by
  cases b <;> simp [IsBinary]

lemma binary_min_zero (t : ℝ) (h : IsBinary t) : min t (1 - t) = 0 := by
  rcases h with h | h <;> rw [h] <;> norm_num

lemma binary_le_zero (t z : ℝ) (h : IsBinary t) (h1 : z ≤ t) (h2 : z ≤ 1 - t) : z ≤ 0 := by
  rcases h with h | h <;> rw [h] at h1 h2 <;> linarith

lemma xF_eq_of (x x' : GVar p n F → ℝ) (ha : ∀ a, x (atom a) = x' (atom a))
    (hn : ∀ g, x (node g) = x' (node g)) : xF x = xF x' := by
  unfold xF
  rw [show (fun a => x (atom a)) = (fun a => x' (atom a)) from funext ha,
    show (fun g => x (node g)) = (fun g => x' (node g)) from funext hn]

lemma mkPt_xF_bin (α : Atom p n → Bool) (yv : {a : Atom p n // 1 ≤ a.1.val} → Bool → ℝ) :
    IsBinary (xF (mkPt F α yv)) :=
  (lsys_binary F _ _ (fun a => bin_bv (α a)) (Wn_spec α).2).2

lemma mkPt_xF_iff (α : Atom p n → Bool) (yv : {a : Atom p n // 1 ≤ a.1.val} → Bool → ℝ) :
    xF (mkPt F α yv) = 1 ↔ F.eval α = true :=
  ((JeroslowMLP.Value.lemma_3_1 p n F α).2 _ (Wn_spec α).1 (Wn_spec α).2).symm

lemma mkPt_S1 (α : Atom p n → Bool) (yv : {a : Atom p n // 1 ≤ a.1.val} → Bool → ℝ)
    (hy : ∀ g s, 0 ≤ yv g s ∧ yv g s ≤ 1) : mkPt F α yv ∈ (jGame p n F).solSet 1 := by
  have hfe : mkPt F α yv ∈ jFeasible p n F := by
    refine ⟨?_, (Wn_spec α).2, rfl, ?_, ?_, ?_⟩
    · intro a; show 0 ≤ (if α a then (1:ℝ) else 0) ∧ (if α a then (1:ℝ) else 0) ≤ 1
      split_ifs <;> norm_num
    · intro g s
      show 2 * yv g s - gArg (mkPt F α yv) g s ≤ |2 * yv g s - (if s then 1 - (if α g.1 then 1 else 0) else (if α g.1 then 1 else 0))| ∧ _
      refine ⟨le_abs_self _, neg_le_abs _, hy g s⟩
    · intro a
      show (0:ℝ) ≤ (if α a.1 then 1 else 0) ∧ (0:ℝ) ≤ 1 - (if α a.1 then 1 else 0)
      split_ifs <;> norm_num
    · have hb := mkPt_xF_bin (F := F) α yv
      show (0:ℝ) ≤ _ ∧ (0:ℝ) ≤ _
      rcases hb with h | h <;> rw [h] <;> norm_num
  refine ⟨hfe, ?_⟩
  intro x' hx' hag
  have hag' : ∀ v, 0 < jOwner v → x' v = mkPt F α yv v := hag
  have hA : ∀ a, x' (atom a) = if α a then 1 else 0 := fun a =>
    hag' (atom a) (by show 0 < a.1.val + 1; omega)
  have hY : ∀ g s, x' (gy g s) = yv g s := fun g s => hag' (gy g s) (by show 0 < 1; norm_num)
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hx'
  have hAf : (fun a => x' (atom a)) = (fun a => if α a then (1:ℝ) else 0) := funext hA
  rw [hAf] at c2
  have hNb := (lsys_binary F _ _ (fun a => bin_bv (α a)) c2).1
  have hN : (fun g => x' (node g)) = Wn F α :=
    (JeroslowMLP.Value.lemma_3_1 p n F α).1.unique ⟨hNb, c2⟩ (Wn_spec α)
  have hxF : xF x' = xF (mkPt F α yv) := by
    apply xF_eq_of
    · intro a; rw [hA]; rfl
    · intro g; rw [show x' (node g) = Wn F α g from congrFun hN g]; rfl
  unfold MultilevelProgram.crit
  apply Finset.sum_le_sum
  intro v _
  cases v with
  | atom a => show jCost p n F 0 (atom a) * _ ≤ jCost p n F 0 (atom a) * _; simp [jCost]
  | node g =>
    show jCost p n F 0 (node g) * _ ≤ jCost p n F 0 (node g) * _
    rw [show x' (node g) = Wn F α g from congrFun hN g]; rfl
  | one => show jCost p n F 0 one * _ ≤ jCost p n F 0 one * _; simp [jCost]
  | gy g s => show jCost p n F 0 (gy g s) * _ ≤ jCost p n F 0 (gy g s) * _; simp [jCost]
  | gz g s =>
    show jCost p n F 0 (gz g s) * _ ≤ jCost p n F 0 (gz g s) * _
    simp only [jCost, one_mul]
    obtain ⟨d1, d2, -, -⟩ := c4 g s
    unfold gArg at d1 d2
    rw [hY, hA] at d1 d2
    show |2 * yv g s - (if s then 1 - (if α g.1 then 1 else 0) else (if α g.1 then 1 else 0))| ≤ _
    exact abs_le.2 ⟨by linarith, d1⟩
  | fz a =>
    show jCost p n F 0 (fz a) * _ ≤ jCost p n F 0 (fz a) * _
    simp only [jCost]
    obtain ⟨d1, d2⟩ := c5 a
    rw [hA] at d1 d2
    have := binary_le_zero _ _ (bin_bv (α a.1)) d1 d2
    show (-1) * (0:ℝ) ≤ -1 * x' (fz a)
    linarith
  | fzF =>
    show jCost p n F 0 fzF * _ ≤ jCost p n F 0 fzF * _
    simp only [jCost]
    rw [hxF] at c6
    have := binary_le_zero _ _ (mkPt_xF_bin α yv) c6.1 c6.2
    show (-1) * (0:ℝ) ≤ -1 * x' fzF
    linarith

lemma setBlock_self (v α : Atom p n → Bool) (b : Fin p) (h : ∀ a : Atom p n, a.1 ≠ b → α a = v a) :
    α = setBlock v b (fun j => α ⟨b, j⟩) := by
  funext ⟨k', j'⟩
  unfold setBlock
  by_cases hk : k' = b
  · subst hk; simp
  · rw [dif_neg hk]; exact h _ hk

lemma setBlock_ne (v : Atom p n → Bool) (b : Fin p) (β : Fin (n b) → Bool) (a : Atom p n)
    (h : a.1 ≠ b) : setBlock v b β a = v a := by
  unfold setBlock; rw [dif_neg h]

/-- `Tf E t`: `1 - t` for an existential, `t` for a universal quantifier. -/
def Tf (E : Prop) [Decidable E] (t : ℝ) : ℝ := if E then 1 - t else t

lemma qlogic {B : Type} (E : Prop) [Decidable E] (Q : B → Prop) (bs : B)
    (hch : if E then ((∃ β, Q β) → Q bs) else ((∃ β, ¬ Q β) → ¬ Q bs))
    (ts : ℝ) (hts : IsBinary ts) (htsq : ts = 1 ↔ Q bs) :
    (∀ (b' : B) (t : ℝ), IsBinary t → (t = 1 ↔ Q b') → Tf E ts ≤ Tf E t) ∧
    (∀ (b' : B) (t : ℝ), IsBinary t → (t = 1 ↔ Q b') → Tf E t ≤ Tf E ts →
      (t = 1 ↔ if E then ∃ β, Q β else ∀ β, Q β)) := by
  unfold Tf
  by_cases hE : E
  · simp only [hE, if_true] at hch ⊢
    constructor
    · intro b' t ht htq
      by_cases hq : Q b'
      · have := htsq.2 (hch ⟨b', hq⟩); rw [this]; rcases ht with h | h <;> rw [h] <;> norm_num
      · rcases ht with h | h
        · rw [h]; rcases hts with h' | h' <;> rw [h'] <;> norm_num
        · exact absurd (htq.1 h) hq
    · intro b' t ht htq hle
      constructor
      · intro h; exact ⟨b', htq.1 h⟩
      · intro hex
        have h1 := htsq.2 (hch hex)
        rw [h1] at hle
        rcases ht with h | h
        · rw [h] at hle; norm_num at hle
        · exact h
  · simp only [hE, if_false] at hch ⊢
    constructor
    · intro b' t ht htq
      by_cases hq : Q b'
      · rcases ht with h | h
        · exact absurd (htq.2 hq) (by rw [h]; norm_num)
        · rw [h]; rcases hts with h' | h' <;> rw [h'] <;> norm_num
      · have : ¬ ts = 1 := fun h => hch ⟨b', hq⟩ (htsq.1 h)
        rcases hts with h' | h'
        · rw [h']; rcases ht with h | h <;> rw [h] <;> norm_num
        · exact absurd h' this
    · intro b' t ht htq hle
      constructor
      · intro h1 β
        by_contra hq
        have : ¬ ts = 1 := fun h => hch ⟨β, hq⟩ (htsq.1 h)
        rcases hts with h' | h'
        · rw [h', h1] at hle; norm_num at hle
        · exact this h'
      · intro hall; exact htq.2 (hall b')

lemma Tf_bounds (E : Prop) [Decidable E] (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ Tf E t ∧ Tf E t ≤ 1 := by
  unfold Tf; split_ifs <;> constructor <;> linarith

lemma Tf_lip (E : Prop) [Decidable E] (s t : ℝ) :
    Tf E t + min t (1 - t) - 2 * |s - t| ≤ Tf E s + min s (1 - s) := by
  unfold Tf
  have ha := le_abs_self (s - t)
  have hb := neg_le_abs (s - t)
  have m1 := min_le_left t (1 - t)
  have m2 := min_le_right t (1 - t)
  rcases min_cases s (1 - s) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> split_ifs <;> linarith

lemma length_pos : ∀ (G : Formula (Atom p n)), (1 : ℝ) ≤ (G.length : ℝ)
  | .var _ => by simp [Formula.length]
  | .neg G => by simp only [Formula.length]; push_cast; linarith [length_pos G]
  | .and G H => by simp only [Formula.length]; push_cast; linarith [length_pos G, length_pos H]
  | .or G H => by simp only [Formula.length]; push_cast; linarith [length_pos G, length_pos H]

/-- Coefficients of player 1's criterion beyond `x(F)`, `u` and `fzF`. -/
noncomputable def e1 (F : Formula (Atom p n)) : GVar p n F → ℝ
  | fz _ => 10 * (F.length : ℝ)
  | gz _ _ => -1
  | _ => 0

lemma crit_one (x : GVar p n F → ℝ) :
    (jGame p n F).crit 1 x =
      (if Even (p - 1) then x one - xF x else xF x) + x fzF + ∑ v, e1 F v * x v := by
  rw [← xFcoef_sum x]
  unfold MultilevelProgram.crit
  show ∑ v, jCost p n F 1 v * x v = _
  have key : ∀ v : GVar p n F, jCost p n F 1 v * x v =
      (if Even (p - 1) then -1 else 1) * (xFcoef v * x v) +
      ((if v = one then (if Even (p - 1) then x one else 0) else 0) +
      ((if v = fzF then x fzF else 0) + e1 F v * x v)) := by
    intro v
    simp only [jCost]
    cases v with
    | one => simp [e1]; split_ifs <;> ring
    | fzF => simp [e1, xFcoef]
    | fz a => simp [e1, xFcoef]
    | gz g s => simp [e1, xFcoef]
    | _ => simp [e1]
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  split_ifs <;> ring

end JML44

namespace JML44

open JMLC

variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

def Sl (F : Formula (Atom p n)) (k : ℕ) (v : Atom p n → Bool) : Set (GVar p n F → ℝ) :=
  {x | x ∈ (jGame p n F).solSet (k + 1) ∧
    ∀ a : Atom p n, k ≤ a.1.val → x (atom a) = if v a then 1 else 0}

def Good (F : Formula (Atom p n)) (k : ℕ) (v : Atom p n → Bool) : Prop :=
  (Sl F k v).Nonempty ∧ ∀ x ∈ Sl F k v, (∀ a, IsBinary (x (atom a))) ∧
    (∀ g, IsBinary (x (node g))) ∧ (xF x = 1 ↔ QHolds p n F k v)

lemma choice {B : Type} [Nonempty B] (E : Prop) [Decidable E] (Q : B → Prop) :
    ∃ bs : B, if E then ((∃ β, Q β) → Q bs) else ((∃ β, ¬ Q β) → ¬ Q bs) := by
  by_cases hE : E
  · simp only [hE, if_true]
    by_cases hex : ∃ β, Q β
    · obtain ⟨β, hβ⟩ := hex; exact ⟨β, fun _ => hβ⟩
    · exact ⟨Classical.arbitrary B, fun h => absurd h hex⟩
  · simp only [hE, if_false]
    by_cases hex : ∃ β, ¬ Q β
    · obtain ⟨β, hβ⟩ := hex; exact ⟨β, fun _ => hβ⟩
    · exact ⟨Classical.arbitrary B, fun h => absurd h hex⟩

lemma qholds_succ (k : ℕ) (hk : k < p) (v : Atom p n → Bool) :
    QHolds p n F (k + 1) v ↔ (if Even (p - (k + 1)) then
      ∃ β : Fin (n ⟨k, hk⟩) → Bool, QHolds p n F k (setBlock v ⟨k, hk⟩ β)
      else ∀ β : Fin (n ⟨k, hk⟩) → Bool, QHolds p n F k (setBlock v ⟨k, hk⟩ β)) := by
  rw [QHolds, dif_pos hk]

/-- Bounds on the `y`-sums of a block at a point of `S₂`. -/
lemma ysum_bounds (b : Fin p) (hb : 1 ≤ b.val) (x' : GVar p n F → ℝ)
    (hx'2 : x' ∈ (jGame p n F).solSet 2) (j : Fin (n b)) :
    1 ≤ x' (gy ⟨⟨b, j⟩, hb⟩ false) + x' (gy ⟨⟨b, j⟩, hb⟩ true) ∧
    (¬ IsBinary (x' (atom ⟨b, j⟩)) →
      2 ≤ x' (gy ⟨⟨b, j⟩, hb⟩ false) + x' (gy ⟨⟨b, j⟩, hb⟩ true)) := by
  have hfe' : x' ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hx'2
  have ha := hfe'.1 ⟨b, j⟩
  have hyf := (hfe'.2.2.2.1 ⟨⟨b, j⟩, hb⟩ false).2.2
  have hyt := (hfe'.2.2.2.1 ⟨⟨b, j⟩, hb⟩ true).2.2
  have e1 := (JeroslowMLP.Value.eq_4_2 p n F x' hx'2 ⟨⟨b, j⟩, hb⟩ false).1
  have e2 := (JeroslowMLP.Value.eq_4_2 p n F x' hx'2 ⟨⟨b, j⟩, hb⟩ true).1
  unfold gArg at e1 e2
  simp only [Bool.false_eq_true, if_false, if_true] at e1 e2
  constructor
  · by_cases hlt : x' (atom ⟨b, j⟩) < 1
    · rw [e1 ⟨ha.1, hlt⟩]; linarith [hyt.1]
    · rw [e2 ⟨by linarith [ha.2], by linarith⟩]; linarith [hyf.1]
  · intro hnb
    have h0 : x' (atom ⟨b, j⟩) ≠ 0 := fun h => hnb (Or.inl h)
    have h1 : x' (atom ⟨b, j⟩) ≠ 1 := fun h => hnb (Or.inr h)
    have hl : x' (atom ⟨b, j⟩) < 1 := lt_of_le_of_ne ha.2 h1
    have hp : 0 < x' (atom ⟨b, j⟩) := lt_of_le_of_ne ha.1 (Ne.symm h0)
    rw [e1 ⟨ha.1, hl⟩, e2 ⟨by linarith, by linarith⟩]; norm_num

lemma crit_lower (b : Fin p) (hb : 1 ≤ b.val) (x' : GVar p n F → ℝ)
    (hx'2 : x' ∈ (jGame p n F).solSet 2) :
    Tf (Even (p - (b.val + 1))) (xF x') + 2 * (n b : ℝ) ≤ (jGame p n F).crit (b.val + 1) x' ∧
    ((∃ j, ¬ IsBinary (x' (atom ⟨b, j⟩))) →
      Tf (Even (p - (b.val + 1))) (xF x') + 2 * (n b : ℝ) + 2 ≤ (jGame p n F).crit (b.val + 1) x') := by
  have hfe' : x' ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hx'2
  rw [crit_hi b hb x', hfe'.2.2.1]
  have hT : (if Even (p - (b.val + 1)) then 1 - xF x' else xF x') =
      Tf (Even (p - (b.val + 1))) (xF x') := rfl
  rw [hT]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (ysum_bounds b hb x' hx'2 j).1)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  constructor
  · linarith
  · rintro ⟨j0, hj0⟩
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin (n b))), (if j = j0 then (2:ℝ) else 1) ≤
        x' (gy ⟨⟨b, j⟩, hb⟩ false) + x' (gy ⟨⟨b, j⟩, hb⟩ true) := by
      intro j _
      split_ifs with h
      · subst h; exact (ysum_bounds b hb x' hx'2 j).2 hj0
      · exact (ysum_bounds b hb x' hx'2 j).1
    have h2 := Finset.sum_le_sum hle
    have h3 : ∑ j : Fin (n b), (if j = j0 then (2:ℝ) else 1) = (n b : ℝ) + 1 := by
      have : ∀ j : Fin (n b), (if j = j0 then (2:ℝ) else 1) = 1 + (if j = j0 then 1 else 0) := by
        intro j; split_ifs <;> norm_num
      simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    linarith

/-- The induction step of Lemma 4.4. -/
lemma step (k : ℕ) (hk1 : 1 ≤ k) (hkp : k + 1 ≤ p) (IH : ∀ v, Good F k v)
    (v : Atom p n → Bool) : Good F (k + 1) v := by
  have hkp' : k < p := by omega
  set b : Fin p := ⟨k, hkp'⟩ with hbdef
  have hb : 1 ≤ b.val := hk1
  set E : Prop := Even (p - (k + 1)) with hE
  let Q : (Fin (n b) → Bool) → Prop := fun β => QHolds p n F k (setBlock v b β)
  have hQ : QHolds p n F (k + 1) v ↔ (if E then ∃ β, Q β else ∀ β, Q β) := qholds_succ k hkp' v
  obtain ⟨bs, hch⟩ := choice E Q
  set vs := setBlock v b bs with hvs
  obtain ⟨x0, hx0⟩ := (IH vs).1
  obtain ⟨hA0, hN0, hF0⟩ := (IH vs).2 x0 hx0
  have hx0k : x0 ∈ (jGame p n F).solSet (k + 1) := hx0.1
  have hfe0 : x0 ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hx0k
  have hx02 : x0 ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ (by omega) hx0k
  -- flip the redundant `y = 1` of block `b`
  let σ : {a : Atom p n // 1 ≤ a.1.val} → Bool → Prop :=
    fun g s => g.1.1 = b ∧ x0 (gy g s) = 1
  have hσ : ∀ i < k + 1, ∀ g s, σ g s → jCost p n F i (gy g s) = 0 := by
    rintro i hi g s ⟨hg, -⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => simp [jCost, xFcoef]
    | i'' + 2, hi'' =>
      have : g.1.1.val + 1 ≠ i'' + 2 := by rw [hg]; show k + 1 ≠ i'' + 2; omega
      simp only [jCost, xFcoef, mul_zero, zero_add]
      split_ifs <;> rfl
  set xs := flipY σ x0 with hxs
  have hxsk : xs ∈ (jGame p n F).solSet (k + 1) := flipY_solSet σ (k + 1) hσ x0 hx0k
  have hxs2 : xs ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ (by omega) hxsk
  have hxsA : ∀ a, xs (atom a) = x0 (atom a) := fun a => rfl
  have hxsF : xF xs = xF x0 := flipY_xF σ x0
  have hys : ∀ j, xs (gy ⟨⟨b, j⟩, hb⟩ false) + xs (gy ⟨⟨b, j⟩, hb⟩ true) = 1 := by
    intro j
    have hyv : ∀ s, (gArg x0 ⟨⟨b, j⟩, hb⟩ s < 1 → xs (gy ⟨⟨b, j⟩, hb⟩ s) = 1) ∧
        (gArg x0 ⟨⟨b, j⟩, hb⟩ s = 1 → xs (gy ⟨⟨b, j⟩, hb⟩ s) = 0) := by
      intro s
      have hξ : 0 ≤ gArg x0 ⟨⟨b, j⟩, hb⟩ s := by
        unfold gArg; have := hfe0.1 ⟨b, j⟩; split_ifs <;> linarith [this.1, this.2]
      constructor
      · intro hlt
        have := (JeroslowMLP.Value.eq_4_2 p n F xs hxs2 ⟨⟨b, j⟩, hb⟩ s).1
        rw [flipY_gArg] at this
        exact this ⟨hξ, hlt⟩
      · intro h1
        rcases (JeroslowMLP.Value.eq_4_2 p n F x0 hx02 ⟨⟨b, j⟩, hb⟩ s).2 h1 with h0 | h1'
        · show flipY σ x0 (gy _ s) = 0
          simp only [flipY]
          rw [if_neg (fun hh => by have h5 : x0 (gy _ s) = 1 := hh.1.2; rw [h0] at h5; norm_num at h5)]
          exact h0
        · show flipY σ x0 (gy _ s) = 0
          simp only [flipY]
          rw [if_pos ⟨⟨rfl, h1'⟩, h1⟩, h1']; ring
    have hwj := hA0 ⟨b, j⟩
    unfold gArg at hyv
    simp only [Bool.false_eq_true, if_false, if_true] at hyv
    rcases hwj with h | h
    · rw [(hyv false).1 (by rw [h]; norm_num), (hyv true).2 (by rw [h]; norm_num)]; ring
    · rw [(hyv false).2 h, (hyv true).1 (by rw [h]; norm_num)]; ring
  have hcrits : (jGame p n F).crit (k + 1) xs = Tf E (xF x0) + 2 * (n b : ℝ) := by
    have hc := crit_hi b hb xs
    rw [hc, show xs one = 1 from hfe0.2.2.1, hxsF]
    simp only [hys, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rfl
  -- upper atoms of xs
  have hxsU : ∀ a : Atom p n, k + 1 ≤ a.1.val → xs (atom a) = if v a then 1 else 0 := by
    intro a ha
    rw [hxsA, hx0.2 a (by omega), hvs, setBlock_ne]
    intro h; rw [h] at ha; exact absurd ha (by show ¬ (k + 1 ≤ k); omega)
  have hFbin0 : IsBinary (xF x0) :=
    (lsys_binary F _ _ hA0 hfe0.2.1).2
  obtain ⟨ql1, ql2⟩ := qlogic E Q bs hch (xF x0) hFbin0 hF0
  -- analysis of a competitor with the same upper blocks
  have hcomp : ∀ x' ∈ (jGame p n F).solSet (k + 1),
      (∀ a : Atom p n, k + 1 ≤ a.1.val → x' (atom a) = if v a then 1 else 0) →
      ((∃ j, ¬ IsBinary (x' (atom ⟨b, j⟩))) →
        (jGame p n F).crit (k + 1) xs < (jGame p n F).crit (k + 1) x') ∧
      ((∀ j, IsBinary (x' (atom ⟨b, j⟩))) →
        (∀ a, IsBinary (x' (atom a))) ∧ (∀ g, IsBinary (x' (node g))) ∧
        ∃ β, (xF x' = 1 ↔ Q β) ∧ IsBinary (xF x') ∧
        Tf E (xF x') + 2 * (n b : ℝ) ≤ (jGame p n F).crit (k + 1) x') := by
    intro x' hx' hU
    have hx'2 : x' ∈ (jGame p n F).solSet 2 := solSet_anti _ 2 _ (by omega) hx'
    have hfe' : x' ∈ jFeasible p n F := solSet_anti _ 0 _ (by omega) hx'
    have hlow := crit_lower b hb x' hx'2
    constructor
    · intro hfr
      have h1 := hlow.2 hfr
      have hb' := lsys_bounds F _ _ hfe'.1 hfe'.2.1
      have := (Tf_bounds E (xF x') hb'.1 hb'.2).1
      have := (Tf_bounds E (xF x0) (lsys_bounds F _ _ hfe0.1 hfe0.2.1).1
        (lsys_bounds F _ _ hfe0.1 hfe0.2.1).2).2
      rw [hcrits]
      exact lt_of_lt_of_le (by linarith) h1
    · intro hbin
      set v' : Atom p n → Bool := fun a => if a.1 = b then decide (x' (atom a) = 1) else v a with hv'
      have hsl : x' ∈ Sl F k v' := by
        refine ⟨hx', fun a ha => ?_⟩
        by_cases hab : a.1 = b
        · have : a = ⟨b, Fin.cast (by rw [hab]) a.2⟩ := by
            obtain ⟨k', j'⟩ := a; simp only at hab; subst hab; rfl
          have hbi := hbin (Fin.cast (by rw [hab]) a.2)
          rw [← this] at hbi
          simp only [hv', hab, if_true]
          rcases hbi with h | h <;> simp [h]
        · have hk' : k + 1 ≤ a.1.val := by
            have : a.1.val ≠ k := fun h => hab (Fin.ext h)
            omega
          simp only [hv', hab, if_false]
          exact hU a hk'
      obtain ⟨hA', hN', hF'⟩ := (IH v').2 x' hsl
      have hv'eq : v' = setBlock v b (fun j => v' ⟨b, j⟩) := by
        apply setBlock_self
        intro a hab
        simp only [hv', hab, if_false]
      refine ⟨hA', hN', fun j => v' ⟨b, j⟩, ?_, (lsys_binary F _ _ hA' hfe'.2.1).2, hlow.1⟩
      rw [hF']
      show QHolds p n F k v' ↔ QHolds p n F k (setBlock v b (fun j => v' ⟨b, j⟩))
      rw [← hv'eq]
  refine ⟨⟨xs, ⟨⟨hxsk, ?_⟩, hxsU⟩⟩, ?_⟩
  · intro x' hx' hag
    have hU : ∀ a : Atom p n, k + 1 ≤ a.1.val → x' (atom a) = if v a then 1 else 0 := by
      intro a ha
      rw [hag (atom a) (by show k + 1 < a.1.val + 1; omega)]
      exact hxsU a ha
    obtain ⟨hc1, hc2⟩ := hcomp x' hx' hU
    by_cases hbin : ∀ j, IsBinary (x' (atom ⟨b, j⟩))
    · obtain ⟨-, -, β, hβ, hbF, hle⟩ := hc2 hbin
      have := ql1 β (xF x') hbF hβ
      rw [hcrits]; linarith
    · push Not at hbin
      exact le_of_lt (hc1 hbin)
  · intro x hx
    have hxk : x ∈ (jGame p n F).solSet (k + 1) := hx.1.1
    have hU := hx.2
    have hle : (jGame p n F).crit (k + 1) x ≤ (jGame p n F).crit (k + 1) xs := by
      apply hx.1.2 xs hxsk
      intro w hw
      cases w with
      | atom a =>
        have ha : k + 1 ≤ a.1.val := by have : k + 1 < a.1.val + 1 := hw; omega
        rw [hxsU a ha, hU a ha]
      | gy g s => exact absurd hw (by show ¬ (k + 1 < 1); omega)
      | _ => exact absurd hw (by show ¬ (k + 1 < 0); omega)
    obtain ⟨hc1, hc2⟩ := hcomp x hxk hU
    have hbin : ∀ j, IsBinary (x (atom ⟨b, j⟩)) := by
      by_contra hh
      push Not at hh
      exact absurd (hc1 hh) (not_lt.2 hle)
    obtain ⟨hA, hN, β, hβ, hbF, hlow⟩ := hc2 hbin
    refine ⟨hA, hN, ?_⟩
    rw [hQ]
    exact ql2 β (xF x) hbF hβ (by linarith)

end JML44

namespace JML44

open JMLC

variable {p : ℕ} {n : Fin p → ℕ} {F : Formula (Atom p n)}

lemma round_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |t - (if decide (1 / 2 ≤ t) then 1 else 0)| ≤ min t (1 - t) := by
  by_cases h : (1:ℝ) / 2 ≤ t
  · simp only [h, decide_true, if_true]
    rw [min_eq_right (by linarith), abs_of_nonpos (by linarith)]; linarith
  · simp only [h, decide_false, Bool.false_eq_true, if_false]
    push Not at h
    rw [min_eq_left (by linarith), sub_zero, abs_of_nonneg h0]

/-- The base case `k = 1` of Lemma 4.4. -/
lemma base (hp : 1 ≤ p) (v : Atom p n → Bool) : Good F 1 v := by
  set b0 : Fin p := ⟨0, hp⟩ with hb0
  set E : Prop := Even (p - 1) with hE
  let Q : (Fin (n b0) → Bool) → Prop := fun β => F.eval (setBlock v b0 β) = true
  have hQ : QHolds p n F 1 v ↔ (if E then ∃ β, Q β else ∀ β, Q β) := qholds_succ 0 hp v
  obtain ⟨bs, hch⟩ := choice E Q
  set αs := setBlock v b0 bs with hαs
  set xs : GVar p n F → ℝ := mkPt F αs (fun _ _ => 1) with hxsdef
  have hxs1 : xs ∈ (jGame p n F).solSet 1 :=
    mkPt_S1 αs _ (fun _ _ => ⟨by norm_num, le_rfl⟩)
  have hFs : IsBinary (xF xs) := mkPt_xF_bin αs _
  have hFsq : xF xs = 1 ↔ Q bs := mkPt_xF_iff αs _
  obtain ⟨ql1, ql2⟩ := qlogic E Q bs hch (xF xs) hFs hFsq
  have hupper : ∀ a : Atom p n, a.1 ≠ b0 ↔ 1 ≤ a.1.val := by
    intro a; constructor
    · intro h; by_contra h'; exact h (Fin.ext (by show a.1.val = 0; omega))
    · intro h h'; rw [h'] at h; exact absurd h (by show ¬ (1 ≤ 0); omega)
  have hxsU : ∀ a : Atom p n, 1 ≤ a.1.val → xs (atom a) = if v a then 1 else 0 := by
    intro a ha
    show (if αs a then (1:ℝ) else 0) = _
    rw [hαs, setBlock_ne _ _ _ _ ((hupper a).2 ha)]
  -- criterion of player 1 on S₁
  have hcrit1 : ∀ x' ∈ (jGame p n F).solSet 1, (jGame p n F).crit 1 x' =
      Tf E (xF x') + min (xF x') (1 - xF x') + ∑ w, e1 F w * x' w := by
    intro x' hx'
    rw [crit_one x', (JeroslowMLP.Value.bookkeeper_in_S1 p n F x' hx').2.2, hx'.1.2.2.1]
    rfl
  have hcrits : (jGame p n F).crit 1 xs = Tf E (xF xs) + ∑ w, e1 F w * xs w := by
    rw [hcrit1 xs hxs1, binary_min_zero _ hFs, add_zero]
  have hL := length_pos F
  -- termwise comparison of the remaining terms
  have hdiff : ∀ x' ∈ (jGame p n F).solSet 1,
      (∀ a : Atom p n, 1 ≤ a.1.val → x' (atom a) = if v a then 1 else 0) →
      ∀ w, 0 ≤ e1 F w * x' w - e1 F w * xs w ∧
        ∀ a0 : {a : Atom p n // a.1.val = 0}, w = fz a0 →
          e1 F w * x' w - e1 F w * xs w =
            10 * (F.length : ℝ) * min (x' (atom a0.1)) (1 - x' (atom a0.1)) := by
    intro x' hx' hU w
    have hbk := JeroslowMLP.Value.bookkeeper_in_S1 p n F x' hx'
    have hfe' := hx'.1
    cases w with
    | fz a =>
      have hz : x' (fz a) = min (x' (atom a.1)) (1 - x' (atom a.1)) := hbk.2.1 a
      have hxz : xs (fz a) = 0 := rfl
      have ha := hfe'.1 a.1
      refine ⟨?_, ?_⟩
      · show 0 ≤ 10 * (F.length : ℝ) * x' (fz a) - 10 * (F.length : ℝ) * xs (fz a)
        rw [hz, hxz]
        have : 0 ≤ min (x' (atom a.1)) (1 - x' (atom a.1)) := le_min ha.1 (by linarith [ha.2])
        have : (0:ℝ) ≤ 10 * F.length := by positivity
        nlinarith
      · rintro a0 h
        simp only [GVar.fz.injEq] at h
        subst h
        show 10 * (F.length : ℝ) * x' (fz a) - 10 * (F.length : ℝ) * xs (fz a) = _
        rw [hz, hxz]; ring
    | gz g s =>
      refine ⟨?_, fun a0 h => by simp at h⟩
      show 0 ≤ (-1) * x' (gz g s) - (-1) * xs (gz g s)
      have hgA : gArg x' g s = gArg xs g s := by
        unfold gArg; rw [hU g.1 g.2, hxsU g.1 g.2]
      have hξ : 0 ≤ gArg xs g s ∧ gArg xs g s ≤ 1 := by
        unfold gArg; have := hxs1.1.1 g.1; split_ifs <;> constructor <;> linarith [this.1, this.2]
      have hxsz : xs (gz g s) = |2 * 1 - gArg xs g s| := rfl
      rw [hbk.1 g s, hxsz, hgA, abs_of_nonneg (by linarith [hξ.2] : (0:ℝ) ≤ 2 * 1 - gArg xs g s)]
      have hy := (hfe'.2.2.2.1 g s).2.2
      have : |2 * x' (gy g s) - gArg xs g s| ≤ 2 - gArg xs g s :=
        abs_le.2 ⟨by linarith [hy.1], by linarith [hy.2]⟩
      linarith
    | _ => exact ⟨by simp [e1], fun a0 h => by simp at h⟩
  -- analysis of a competitor
  have hcomp : ∀ x' ∈ (jGame p n F).solSet 1,
      (∀ a : Atom p n, 1 ≤ a.1.val → x' (atom a) = if v a then 1 else 0) →
      ((∃ a, ¬ IsBinary (x' (atom a))) →
        (jGame p n F).crit 1 xs < (jGame p n F).crit 1 x') ∧
      ((∀ a, IsBinary (x' (atom a))) →
        (∀ g, IsBinary (x' (node g))) ∧
        ∃ β, (xF x' = 1 ↔ Q β) ∧ IsBinary (xF x') ∧
        Tf E (xF x') + ∑ w, e1 F w * xs w ≤ (jGame p n F).crit 1 x') := by
    intro x' hx' hU
    have hfe' := hx'.1
    have hdf := hdiff x' hx' hU
    have hsum0 : ∑ w, e1 F w * xs w ≤ ∑ w, e1 F w * x' w := by
      apply Finset.sum_le_sum; intro w _; linarith [(hdf w).1]
    have hc' := hcrit1 x' hx'
    have hFb : 0 ≤ xF x' ∧ xF x' ≤ 1 := lsys_bounds F _ _ hfe'.1 hfe'.2.1
    have hmin0 : 0 ≤ min (xF x') (1 - xF x') := le_min hFb.1 (by linarith [hFb.2])
    constructor
    · rintro ⟨a1, ha1⟩
      set f : Atom p n → ℝ := fun a => min (x' (atom a)) (1 - x' (atom a)) with hf
      obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ f ⟨a1, Finset.mem_univ _⟩
      have hfa1 : 0 < f a1 := by
        have h := hfe'.1 a1
        have h0 : x' (atom a1) ≠ 0 := fun hh => ha1 (Or.inl hh)
        have h1 : x' (atom a1) ≠ 1 := fun hh => ha1 (Or.inr hh)
        exact lt_min (lt_of_le_of_ne h.1 (Ne.symm h0)) (by linarith [lt_of_le_of_ne h.2 h1])
      set δ := f a0 with hδ
      have hδpos : 0 < δ := lt_of_lt_of_le hfa1 (ha0 a1 (Finset.mem_univ _))
      have ha00 : a0.1.val = 0 := by
        by_contra hne
        have hu : 1 ≤ a0.1.val := by omega
        have : f a0 = 0 := by
          show min (x' (atom a0)) (1 - x' (atom a0)) = 0
          rw [hU a0 hu]; exact binary_min_zero _ (bin_bv _)
        linarith
      set α0 : Atom p n → Bool := fun a => decide (1 / 2 ≤ x' (atom a)) with hα0
      have hα0U : ∀ a : Atom p n, a.1 ≠ b0 → α0 a = v a := by
        intro a ha
        simp only [hα0]
        rw [hU a ((hupper a).1 ha)]
        cases v a <;> norm_num
      have hα0eq := setBlock_self v α0 b0 hα0U
      have h49 : ∀ a ∈ F.atoms, |x' (atom a) - (if α0 a then 1 else 0)| < 2 * δ := by
        intro a _
        have h := hfe'.1 a
        calc |x' (atom a) - (if α0 a then 1 else 0)| ≤ f a := round_le _ h.1 h.2
          _ ≤ δ := ha0 a (Finset.mem_univ _)
          _ < 2 * δ := by linarith
      have h41 := JeroslowMLP.Value.lemma_4_1 F (2 * δ) (2 * δ * F.length) (by linarith)
        (by positivity) le_rfl α0 (fun a => x' (atom a)) (fun g => x' (node g)) h49 hfe'.2.1
      set t0 : ℝ := if F.eval α0 then 1 else 0 with ht0
      have ht0b : IsBinary t0 := bin_bv _
      have ht0q : t0 = 1 ↔ Q (fun j => α0 ⟨b0, j⟩) := by
        show t0 = 1 ↔ F.eval (setBlock v b0 (fun j => α0 ⟨b0, j⟩)) = true
        rw [← hα0eq, ht0]; cases F.eval α0 <;> simp
      have hq1 := ql1 _ t0 ht0b ht0q
      have hlip := Tf_lip E (xF x') t0
      rw [binary_min_zero _ ht0b] at hlip
      have habs : |xF x' - t0| < 2 * δ * F.length := h41
      have hfzd := (hdf (fz ⟨a0, ha00⟩)).2 ⟨a0, ha00⟩ rfl
      have hsingle : e1 F (fz ⟨a0, ha00⟩) * x' (fz ⟨a0, ha00⟩) - e1 F (fz ⟨a0, ha00⟩) * xs (fz ⟨a0, ha00⟩)
          ≤ ∑ w, (e1 F w * x' w - e1 F w * xs w) :=
        Finset.single_le_sum (f := fun w => e1 F w * x' w - e1 F w * xs w)
          (fun w _ => (hdf w).1) (Finset.mem_univ _)
      rw [Finset.sum_sub_distrib] at hsingle
      rw [hfzd] at hsingle
      have hδL : 0 < δ * F.length := by positivity
      rw [hc', hcrits]
      have : 10 * (F.length : ℝ) * min (x' (atom a0)) (1 - x' (atom a0)) = 10 * (δ * F.length) := by
        rw [hδ]; ring
      linarith
    · intro hbin
      have hN := (lsys_binary F _ _ hbin hfe'.2.1).1
      set α' : Atom p n → Bool := fun a => decide (x' (atom a) = 1) with hα'
      have hAf : (fun a => x' (atom a)) = fun a => if α' a then (1:ℝ) else 0 := by
        funext a; rcases hbin a with h | h <;> simp [hα', h]
      have hsys := hfe'.2.1
      rw [hAf] at hsys
      have h31 := (JeroslowMLP.Value.lemma_3_1 p n F α').2 _ hN hsys
      have hα'U : ∀ a : Atom p n, a.1 ≠ b0 → α' a = v a := by
        intro a ha
        simp only [hα']
        rw [hU a ((hupper a).1 ha)]
        cases v a <;> norm_num
      have hα'eq := setBlock_self v α' b0 hα'U
      refine ⟨hN, fun j => α' ⟨b0, j⟩, ?_, (lsys_binary F _ _ hbin hfe'.2.1).2, ?_⟩
      · show xF x' = 1 ↔ F.eval (setBlock v b0 (fun j => α' ⟨b0, j⟩)) = true
        rw [← hα'eq, h31]
        unfold xF; rw [hAf]
      · rw [hc']; linarith
  refine ⟨⟨xs, ⟨⟨hxs1, ?_⟩, hxsU⟩⟩, ?_⟩
  · intro x' hx' hag
    have hU : ∀ a : Atom p n, 1 ≤ a.1.val → x' (atom a) = if v a then 1 else 0 := by
      intro a ha
      rw [hag (atom a) (by show 1 < a.1.val + 1; omega)]
      exact hxsU a ha
    obtain ⟨hc1, hc2⟩ := hcomp x' hx' hU
    by_cases hbin : ∀ a, IsBinary (x' (atom a))
    · obtain ⟨-, β, hβ, hbF, hle⟩ := hc2 hbin
      have := ql1 β (xF x') hbF hβ
      rw [hcrits]; linarith
    · push Not at hbin
      exact le_of_lt (hc1 hbin)
  · intro x hx
    have hx1 : x ∈ (jGame p n F).solSet 1 := hx.1.1
    have hU := hx.2
    have hle : (jGame p n F).crit 1 x ≤ (jGame p n F).crit 1 xs := by
      apply hx.1.2 xs hxs1
      intro w hw
      cases w with
      | atom a =>
        have ha : 1 ≤ a.1.val := by have : 1 < a.1.val + 1 := hw; omega
        rw [hxsU a ha, hU a ha]
      | gy g s => exact absurd hw (by show ¬ (1 < 1); omega)
      | _ => exact absurd hw (by show ¬ (1 < 0); omega)
    obtain ⟨hc1, hc2⟩ := hcomp x hx1 hU
    have hbin : ∀ a, IsBinary (x (atom a)) := by
      by_contra hh
      push Not at hh
      exact absurd (hc1 hh) (not_lt.2 hle)
    obtain ⟨hN, β, hβ, hbF, hlow⟩ := hc2 hbin
    refine ⟨hbin, hN, ?_⟩
    rw [hQ]
    exact ql2 β (xF x) hbF hβ (by rw [hcrits] at hle; linarith)

end JML44

open JML44

theorem solution (p : ℕ) (n : Fin p → ℕ) (F : Formula (Atom p n)) (k : ℕ)
    (hk1 : 1 ≤ k) (hkp : k ≤ p) (v : Atom p n → Bool) :
    let Slice : Set (GVar p n F → ℝ) :=
      {x | x ∈ (jGame p n F).solSet (k + 1) ∧
        ∀ a : Atom p n, k ≤ a.1.val → x (atom a) = if v a then 1 else 0}
    Slice.Nonempty ∧
    ∀ x ∈ Slice, (∀ a, IsBinary (x (atom a))) ∧ (∀ g, IsBinary (x (node g))) ∧
      (xF x = 1 ↔ QHolds p n F k v) := by
  intro Slice
  have key : ∀ k, 1 ≤ k → k ≤ p → ∀ v, Good F k v := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base => intro hp v; exact base hp v
    | succ k hk ih => intro hkp v; exact step k hk hkp (ih (by omega)) v
  exact key k hk1 hkp v
