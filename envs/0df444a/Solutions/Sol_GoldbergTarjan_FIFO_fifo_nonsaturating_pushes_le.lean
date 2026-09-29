-- Prove2me | solution 1 for GoldbergTarjan.FIFO.fifo_nonsaturating_pushes_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:02:58.057167+00:00
-- url     : https://prove2.me/submissions/12152b03-193a-4564-abc8-c50710e63ead

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts



namespace GoldbergTarjan.FIFO

open Classical

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option linter.unusedVariables false

section MF
variable {V : Type} [Fintype V]

noncomputable def unitF (a b : V) : V → V → ℝ :=
  fun x y => (if x = a ∧ y = b then 1 else 0) - (if x = b ∧ y = a then 1 else 0)

lemma excess_unitF (a b u : V) :
    excess (unitF a b) u = (if u = b then 1 else 0) - (if u = a then 1 else 0) := by
  unfold excess unitF
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : u = b
    · simp [h]
    · simp [h]
  · by_cases h : u = a
    · simp [h]
    · simp [h]

lemma unitF_antisymm (a b x y : V) : unitF a b x y = - unitF a b y x := by
  unfold unitF
  have e1 : (if y = a ∧ x = b then (1:ℝ) else 0) = if x = b ∧ y = a then 1 else 0 :=
    if_congr and_comm rfl rfl
  have e2 : (if y = b ∧ x = a then (1:ℝ) else 0) = if x = a ∧ y = b then 1 else 0 :=
    if_congr and_comm rfl rfl
  rw [e1, e2]; ring

lemma excess_add (f g : V → V → ℝ) (u : V) : excess (fun x y => f x y + g x y) u = excess f u + excess g u := by
  unfold excess; rw [Finset.sum_add_distrib]

lemma excess_smul (f : V → V → ℝ) (r : ℝ) (u : V) : excess (fun x y => r * f x y) u = r * excess f u := by
  unfold excess; rw [Finset.mul_sum]

lemma sum_antisymm_zero (g : V → V → ℝ) (hg : ∀ x y, g x y = - g y x) (T : Finset V) :
    ∑ x ∈ T, ∑ y ∈ T, g x y = 0 := by
  have : ∑ x ∈ T, ∑ y ∈ T, g x y = - ∑ x ∈ T, ∑ y ∈ T, g x y := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; congr 1; ext x; rw [← Finset.sum_neg_distrib]
    congr 1; ext y; rw [hg]
  linarith
end MF

section GT
variable {V : Type} [Fintype V] [DecidableEq V]

lemma unitF_nonneg_of {v w x y : V} (h : ¬ (x = w ∧ y = v)) : 0 ≤ unitF v w x y := by
  unfold unitF; rw [if_neg h]; split_ifs <;> norm_num

lemma unitF_nonpos_of {v w x y : V} (h : ¬ (x = v ∧ y = w)) : unitF v w x y ≤ 0 := by
  unfold unitF; rw [if_neg h]; split_ifs <;> norm_num

lemma unitF_vw {v w : V} (hvw : v ≠ w) : unitF v w v w = 1 := by
  unfold unitF; rw [if_pos ⟨rfl, rfl⟩, if_neg (fun h => hvw h.1)]; norm_num

lemma pushFlow_apply (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) (x y : V) :
    pushFlow N f v w x y = f x y + pushAmount N f v w * unitF v w x y := by
  unfold pushFlow unitF
  by_cases h1 : x = v ∧ y = w
  · have h2 : ¬ (x = w ∧ y = v) := fun h2 => hvw (h1.1.symm.trans h2.1)
    obtain ⟨rfl, rfl⟩ := h1
    simp only [and_self, if_true, if_neg h2]; ring
  · by_cases h2 : x = w ∧ y = v
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [if_neg h1, and_self, if_true]; ring
    · simp only [if_neg h1, if_neg h2]; ring

lemma pushFlow_eq (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    pushFlow N f v w = fun x y => f x y + pushAmount N f v w * unitF v w x y := by
  funext x y; exact pushFlow_apply N f v w hvw x y

lemma excess_pushFlow (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) (u : V) :
    excess (pushFlow N f v w) u = excess f u +
      pushAmount N f v w * ((if u = w then 1 else 0) - (if u = v then 1 else 0)) := by
  rw [pushFlow_eq N f v w hvw, excess_add, excess_smul (f := unitF v w), excess_unitF]
  congr 3 <;> simp

lemma excess_push_v (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    excess (pushFlow N f v w) v = excess f v - pushAmount N f v w := by
  rw [excess_pushFlow N f v w hvw]; simp [hvw]; ring

lemma excess_push_w (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    excess (pushFlow N f v w) w = excess f w + pushAmount N f v w := by
  rw [excess_pushFlow N f v w hvw]; simp [hvw.symm]

lemma excess_push_other (N : Network V) (f : V → V → ℝ) (v w u : V) (hvw : v ≠ w)
    (hv : u ≠ v) (hw : u ≠ w) :
    excess (pushFlow N f v w) u = excess f u := by
  rw [excess_pushFlow N f v w hvw]; simp [hv, hw]

lemma push_ne {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v w : V}
    (h : PushApplicable N f d v w) : v ≠ w := by
  intro hvw; subst hvw
  obtain ⟨⟨_, _, hfin, _⟩, _, hd⟩ := h
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfin)
  rw [← hk] at hd; norm_cast at hd; omega

lemma pushAmount_pos {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v w : V}
    (h : PushApplicable N f d v w) : 0 < pushAmount N f v w :=
  lt_min h.1.2.2.2 h.2.1

lemma res_push_vw (N : Network V) (f : V → V → ℝ) (v w : V) (hvw : v ≠ w) :
    residual N (pushFlow N f v w) v w = residual N f v w - pushAmount N f v w := by
  unfold residual; rw [pushFlow_apply N f v w hvw, unitF_vw hvw]; ring

lemma res_push_le (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (a b v w : V)
    (hp : PushApplicable N f d a b) (hne : ¬ (a = w ∧ b = v)) :
    residual N (pushFlow N f a b) v w ≤ residual N f v w := by
  have hab := push_ne hp
  have hδ := (pushAmount_pos hp).le
  unfold residual; rw [pushFlow_apply N f a b hab]
  have : 0 ≤ unitF a b v w := unitF_nonneg_of (fun h => hne ⟨h.2.symm, h.1.symm⟩)
  nlinarith [mul_nonneg hδ this]

lemma push_preflow (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V) (hf : IsPreflow N f)
    (hp : PushApplicable N f d v w) : IsPreflow N (pushFlow N f v w) := by
  have hvw := push_ne hp
  have hδ0 := (pushAmount_pos hp).le
  have hδe : pushAmount N f v w ≤ excess f v := min_le_left _ _
  have hδr : pushAmount N f v w ≤ residual N f v w := min_le_right _ _
  refine ⟨?_, ?_, ?_⟩
  · intro x y; rw [pushFlow_apply N f v w hvw]
    by_cases h1 : x = v ∧ y = w
    · obtain ⟨rfl, rfl⟩ := h1; rw [unitF_vw hvw]; unfold residual at hδr; linarith
    · have := unitF_nonpos_of (v := v) (w := w) h1
      nlinarith [hf.1 x y, mul_nonpos_of_nonneg_of_nonpos hδ0 this]
  · intro x y; rw [pushFlow_apply N f v w hvw, pushFlow_apply N f v w hvw, hf.2.1 x y,
      unitF_antisymm v w x y]; ring
  · intro x hx
    by_cases hxv : x = v
    · subst hxv; rw [excess_push_v N f x w hvw]; linarith
    · by_cases hxw : x = w
      · subst hxw; rw [excess_push_w N f v x hvw]; linarith [hf.2.2 x hx]
      · rw [excess_push_other N f v w x hvw hxv hxw]; exact hf.2.2 x hx

lemma reach_source (N : Network V) (f : V → V → ℝ) (hf : IsPreflow N f) (v : V)
    (hv : 0 < excess f v) : ResidualReachable N f v N.s := by
  by_contra hns
  set S : Finset V := Finset.univ.filter (fun u => ResidualReachable N f v u) with hS
  have hvS : v ∈ S := by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact Relation.ReflTransGen.refl
  have hsS : N.s ∉ S := by simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]; exact hns
  have hsum : ∑ x ∈ S, excess f x ≤ 0 := by
    unfold excess
    have h2 : ∀ x, ∑ y, f y x = ∑ y ∈ S, f y x + ∑ y ∈ Sᶜ, f y x :=
      fun x => (Finset.sum_add_sum_compl S _).symm
    simp_rw [h2]; rw [Finset.sum_add_distrib]
    have h3 : ∑ x ∈ S, ∑ y ∈ S, f y x = 0 := by
      rw [Finset.sum_comm]; exact sum_antisymm_zero f hf.2.1 S
    rw [h3, zero_add]
    apply Finset.sum_nonpos; intro x hx; apply Finset.sum_nonpos; intro y hy
    have hxy : ¬ (0 < residual N f x y) := by
      intro he
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at hx hy
      exact hy (hx.tail he)
    unfold residual at hxy; push_neg at hxy
    rw [hf.2.1 y x]; linarith [N.c_nonneg x y]
  have hpos : excess f v ≤ ∑ x ∈ S, excess f x := by
    apply Finset.single_le_sum (f := fun x => excess f x) _ hvS
    intro x hx; apply hf.2.2; intro h; subst h; exact hsS hx
  linarith

lemma label_levels (E : V → V → Prop) (d : V → ℕ∞) (hval : ∀ x y, E x y → d x ≤ d y + 1)
    {v u : V} (h : Relation.ReflTransGen E v u) :
    ∀ ℓ : ℕ, d u ≤ ℓ → (ℓ : ℕ∞) ≤ d v → ∃ x, d x = ℓ := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro ℓ h1 h2; exact ⟨u, le_antisymm h1 h2⟩
  | @head a b hab _ ih =>
    intro ℓ h1 h2
    by_cases h3 : (ℓ : ℕ∞) ≤ d b
    · exact ih ℓ h1 h3
    · push_neg at h3
      refine ⟨a, le_antisymm ?_ h2⟩
      exact (hval _ _ hab).trans (Order.add_one_le_of_lt h3)

lemma label_reach (E : V → V → Prop) (d : V → ℕ∞) (hval : ∀ x y, E x y → d x ≤ d y + 1)
    {v u : V} (h : Relation.ReflTransGen E v u) (a : ℕ) (hu : d u = a) :
    d v ≤ ((a + (Fintype.card V - 1) : ℕ) : ℕ∞) := by
  by_contra hlt
  push_neg at hlt
  have hlev := label_levels E d hval h
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have h5 : ((a + Fintype.card V : ℕ) : ℕ∞) ≤ d v := by
    have := Order.add_one_le_of_lt hlt
    have e : a + Fintype.card V = a + (Fintype.card V - 1) + 1 := by omega
    rw [e]; push_cast at this ⊢; exact this
  have hex : ∀ i : Fin (Fintype.card V + 1), ∃ x, d x = ((a + i : ℕ) : ℕ∞) := by
    intro i
    apply hlev
    · rw [hu]; exact_mod_cast Nat.le_add_right a i
    · refine le_trans ?_ h5; exact_mod_cast (by omega : a + (i:ℕ) ≤ a + Fintype.card V)
  choose g hg using hex
  have hinj : Function.Injective g := by
    intro i j hij
    have := hg i; rw [hij, hg j] at this
    have : a + (j:ℕ) = a + i := by exact_mod_cast this
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective g hinj
  simp at this

/-! ## Invariant -/

structure Inv (N : Network V) (L : V → List V) (σ : Config V) : Prop where
  pre : IsPreflow N σ.f
  valid : ∀ v w, 0 < residual N σ.f v w → σ.d v ≤ σ.d w + 1
  ds : σ.d N.s = (Fintype.card V : ℕ∞)
  bound : ∀ v, σ.d v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)
  cur : ∀ v, ∀ i < σ.cur v, ∀ w, (L v)[i]? = some w → 0 < residual N σ.f v w → σ.d v ≤ σ.d w

lemma card_two_le (N : Network V) : 2 ≤ Fintype.card V := by
  have := Finset.card_le_univ ({N.s, N.t} : Finset V)
  rw [Finset.card_pair N.s_ne_t] at this; exact this

lemma Inv.fin {N : Network V} {L : V → List V} {σ : Config V} (h : Inv N L σ) (v : V) :
    σ.d v ≠ ⊤ := (lt_of_le_of_lt (h.bound v) (ENat.coe_lt_top _)).ne

lemma res_self {N : Network V} {f : V → V → ℝ} (hf : IsPreflow N f) (v : V) :
    residual N f v v = 0 := by
  unfold residual; have := hf.2.1 v v; rw [N.c_self]; linarith

lemma mem_L {N : Network V} {L : V → List V} {f : V → V → ℝ} (hf : IsPreflow N f)
    (hL : IsEdgeList N L) {v w : V} (h : 0 < residual N f v w) : w ∈ L v := by
  rw [(hL v).2]
  unfold residual at h
  by_cases hc : 0 < N.c v w
  · exact Or.inl hc
  · right
    have h0 : N.c v w = 0 := le_antisymm (not_lt.mp hc) (N.c_nonneg v w)
    have := hf.2.1 v w; have := hf.1 w v; linarith

lemma nopush_le {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v w : V}
    (hval : d v ≤ d w + 1) (hact : IsActive N f d v) (hres : 0 < residual N f v w)
    (hnp : ¬ PushApplicable N f d v w) : d v ≤ d w := by
  have hne : d v ≠ d w + 1 := fun h => hnp ⟨hact, hres, h⟩
  have hlt : d v < d w + 1 := lt_of_le_of_ne hval hne
  by_cases hw : d w = ⊤
  · rw [hw]; exact le_top
  · exact (ENat.lt_add_one_iff hw).mp hlt

lemma relabel_applicable {N : Network V} {L : V → List V} {σ : Config V} {v : V}
    (hL : IsEdgeList N L) (hI : Inv N L σ) (hact : IsActive N σ.f σ.d v)
    (hrel : IsRelabelOp N L v σ) : RelabelApplicable N σ.f σ.d v := by
  obtain ⟨w0, hw0, hnp, hlast⟩ := hrel
  refine ⟨hact, fun w hw => ?_⟩
  have hmem := mem_L hI.pre hL hw
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
  have hilt : i < (L v).length := by
    by_contra hc; push_neg at hc; rw [List.getElem?_eq_none hc] at hi; cases hi
  rcases lt_trichotomy i (σ.cur v) with h | h | h
  · exact hI.cur v i h w hi hw
  · subst h; rw [hw0] at hi; cases hi
    exact nopush_le (hI.valid v w0 hw) hact hw hnp
  · omega

lemma exists_res {N : Network V} {f : V → V → ℝ} (hf : IsPreflow N f) {v : V}
    (hv : 0 < excess f v) : ∃ u, 0 < residual N f v u := by
  by_contra hc; push_neg at hc
  have : excess f v ≤ 0 := by
    unfold excess; apply Finset.sum_nonpos; intro u _
    have := hc u; unfold residual at this; have := hf.2.1 u v; linarith [N.c_nonneg v u]
  linarith

lemma relabel_ge {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v : V}
    (ha : RelabelApplicable N f d v) : d v + 1 ≤ relabelLabel N f d v := by
  unfold relabelLabel; apply le_iInf₂; intro w hw; exact add_le_add (ha.2 w hw) le_rfl

lemma relabel_le {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v w : V}
    (hw : 0 < residual N f v w) : relabelLabel N f d v ≤ d w + 1 := iInf₂_le w hw

lemma pr_eq {N : Network V} {L : V → List V} {v w : V} {σ : Config V}
    (hw : (L v)[σ.cur v]? = some w) :
    pushRelabel N L v σ =
      if PushApplicable N σ.f σ.d v w then { σ with f := pushFlow N σ.f v w }
      else if σ.cur v + 1 < (L v).length then
        { σ with cur := Function.update σ.cur v (σ.cur v + 1) }
      else
        { σ with d := Function.update σ.d v (relabelLabel N σ.f σ.d v),
                 cur := Function.update σ.cur v 0 } := by
  simp only [pushRelabel, hw]

theorem step_inv {N : Network V} {L : V → List V} {σ : Config V} {v : V}
    (hL : IsEdgeList N L) (hI : Inv N L σ) (hA : PRApplicable N L v σ) :
    Inv N L (pushRelabel N L v σ) ∧ (∀ x, σ.d x ≤ (pushRelabel N L v σ).d x) ∧
      (IsRelabelOp N L v σ → σ.d v < (pushRelabel N L v σ).d v) := by
  obtain ⟨hact, hcur⟩ := hA
  have hw := List.getElem?_eq_getElem hcur
  set w := (L v)[σ.cur v] with hwdef
  rw [pr_eq hw]
  by_cases hp : PushApplicable N σ.f σ.d v w
  · rw [if_pos hp]
    have hvw := push_ne hp
    have hres : ∀ a b, 0 < residual N (pushFlow N σ.f v w) a b →
        0 < residual N σ.f a b ∨ (a = w ∧ b = v) := by
      intro a b hab
      by_cases h : a = w ∧ b = v
      · exact Or.inr h
      · exact Or.inl (lt_of_lt_of_le hab (res_push_le N σ.f σ.d v w a b hp (fun h' => h ⟨h'.2.symm, h'.1.symm⟩)))
    refine ⟨⟨push_preflow N σ.f σ.d v w hI.pre hp, ?_, hI.ds, hI.bound, ?_⟩,
      fun x => le_rfl, ?_⟩
    · intro a b hab
      rcases hres a b hab with h | ⟨ha, hb⟩
      · exact hI.valid a b h
      · show σ.d a ≤ σ.d b + 1
        rw [ha, hb, hp.2.2]; exact le_self_add.trans le_self_add
    · intro x i hi y hy hxy
      rcases hres x y hxy with h | ⟨ha, hb⟩
      · exact hI.cur x i hi y hy h
      · show σ.d x ≤ σ.d y
        rw [ha, hb, hp.2.2]; exact le_self_add
    · rintro ⟨w', hw', hnp, _⟩
      rw [hw] at hw'; cases hw'; exact absurd hp hnp
  · rw [if_neg hp]
    by_cases hnext : σ.cur v + 1 < (L v).length
    · rw [if_pos hnext]
      refine ⟨⟨hI.pre, hI.valid, hI.ds, hI.bound, ?_⟩, fun x => le_rfl, ?_⟩
      · intro x i hi y hy hxy
        simp only at hi hxy ⊢
        by_cases hx : x = v
        · subst hx
          rw [Function.update_self] at hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact hI.cur x i h y hy hxy
          · subst h; rw [hw] at hy
            have hyw : w = y := Option.some.inj hy
            rw [← hyw] at hxy ⊢
            exact nopush_le (hI.valid x _ hxy) hact hxy hp
        · rw [Function.update_of_ne hx] at hi
          exact hI.cur x i hi y hy hxy
      · rintro ⟨w', hw', hnp, hl⟩; omega
    · rw [if_neg hnext]
      have hlast : σ.cur v + 1 = (L v).length := by omega
      have hrop : IsRelabelOp N L v σ := ⟨w, hw, hp, hlast⟩
      have hra := relabel_applicable hL hI hact hrop
      have hge := relabel_ge hra
      obtain ⟨u, hu⟩ := exists_res hI.pre hact.2.2.2
      have hle := relabel_le (d := σ.d) hu
      set rl := relabelLabel N σ.f σ.d v with hrl
      have hdv_lt : σ.d v < rl := by
        have hfin := hI.fin v
        exact lt_of_lt_of_le ((ENat.lt_add_one_iff hfin).mpr le_rfl) hge
      have hmono : ∀ x, σ.d x ≤ Function.update σ.d v rl x := by
        intro x; by_cases hx : x = v
        · subst hx; rw [Function.update_self]; exact hdv_lt.le
        · rw [Function.update_of_ne hx]
      have hvs : v ≠ N.s := hact.1
      have hvalid : ∀ a b, 0 < residual N σ.f a b →
          Function.update σ.d v rl a ≤ Function.update σ.d v rl b + 1 := by
        intro a b hab
        by_cases ha : a = v
        · subst ha; rw [Function.update_self]
          exact (relabel_le hab).trans (add_le_add (hmono b) le_rfl)
        · rw [Function.update_of_ne ha]
          exact (hI.valid a b hab).trans (add_le_add (hmono b) le_rfl)
      have hds : Function.update σ.d v rl N.s = (Fintype.card V : ℕ∞) := by
        rw [Function.update_of_ne hvs.symm]; exact hI.ds
      refine ⟨⟨hI.pre, hvalid, hds, ?_, ?_⟩, hmono, fun _ => ?_⟩
      · intro x
        by_cases hx : x = v
        · subst hx
          have hr := reach_source N σ.f hI.pre x hact.2.2.2
          have := label_reach (fun a b => 0 < residual N σ.f a b) (Function.update σ.d x rl)
            hvalid hr (Fintype.card V) hds
          refine this.trans ?_
          exact_mod_cast (by omega : Fintype.card V + (Fintype.card V - 1) ≤ 2 * Fintype.card V - 1)
        · simp only; rw [Function.update_of_ne hx]; exact hI.bound x
      · intro x i hi y hy hxy
        simp only at hi hxy ⊢
        by_cases hx : x = v
        · subst hx; rw [Function.update_self] at hi; omega
        · rw [Function.update_of_ne hx] at hi ⊢
          exact (hI.cur x i hi y hy hxy).trans (hmono y)
      · simp only; rw [Function.update_self]; exact hdv_lt


lemma init_inv (N : Network V) (L : V → List V) : Inv N L (initConfig N) := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro v w; simp only [initConfig, initFlow]; split_ifs with h1 h2
    · subst h1; exact le_rfl
    · have := N.c_nonneg N.s v; have := N.c_nonneg v w; linarith
    · exact N.c_nonneg v w
  · intro v w; simp only [initConfig, initFlow]
    by_cases h1 : v = N.s <;> by_cases h2 : w = N.s <;> simp [h1, h2, N.c_self]
  · intro v hv; unfold excess; simp only [initConfig, initFlow]
    rw [Finset.sum_eq_single N.s]
    · simp only [if_true]; exact N.c_nonneg _ _
    · intro b _ hb; simp [hb, hv]
    · simp
  · intro x y hxy; by_cases hx : x = N.s
    · exfalso; subst hx; unfold residual at hxy
      simp [initConfig, initFlow] at hxy
    · simp [initConfig, initLabel, hx]
  · simp [initConfig, initLabel]
  · intro x; simp only [initConfig, initLabel]; split_ifs
    · exact_mod_cast (by omega : Fintype.card V ≤ 2 * Fintype.card V - 1)
    · simp
  · intro v i hi; simp [initConfig] at hi

lemma iter_succ (N : Network V) (L : V → List V) (v : V) (σ : Config V) (j : ℕ) :
    prIter N L v σ (j + 1) = pushRelabel N L v (prIter N L v σ j) := by
  unfold prIter; exact Function.iterate_succ_apply' _ _ _

lemma iter_zero (N : Network V) (L : V → List V) (v : V) (σ : Config V) :
    prIter N L v σ 0 = σ := rfl

lemma disch_inv {N : Network V} {L : V → List V} {v : V} {σ : Config V} {J : ℕ}
    (hL : IsEdgeList N L) (hI : Inv N L σ)
    (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j)) :
    ∀ j ≤ J, Inv N L (prIter N L v σ j) ∧ ∀ x, σ.d x ≤ (prIter N L v σ j).d x := by
  intro j
  induction j with
  | zero => intro _; exact ⟨hI, fun x => le_rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have := step_inv hL h1 (hA j (by omega))
    rw [iter_succ]
    exact ⟨this.1, fun x => (h2 x).trans (this.2.1 x)⟩

lemma front_eq {N : Network V} {L : V → List V} {S S' : State V} {J : ℕ}
    (h : DischargeStep N L S J S') :
    ∃ i rest, S.Q = (frontVertex N S, i) :: rest ∧ 0 < J ∧
      (∀ j < J, PRApplicable N L (frontVertex N S) (prIter N L (frontVertex N S) S.cfg j)) ∧
      S'.cfg = prIter N L (frontVertex N S) S.cfg J := by
  obtain ⟨v, i, rest, hQ, hJ, hA, _, _, hcfg, _⟩ := h
  have hf : frontVertex N S = v := by simp [frontVertex, hQ]
  rw [hf]; exact ⟨i, rest, hQ, hJ, hA, hcfg⟩

section Run
variable {N : Network V} {L : V → List V} {K : ℕ} {S : ℕ → State V} {J : ℕ → ℕ}

lemma run_inv (hrun : IsFIFORun N L K S J) : ∀ k ≤ K, Inv N L (S k).cfg := by
  intro k
  induction k with
  | zero => intro _; rw [hrun.2.1]; exact init_inv N L
  | succ k ih =>
    intro hk
    obtain ⟨i, rest, hQ, hJ, hA, hcfg⟩ := front_eq (hrun.2.2.2 k (by omega))
    rw [hcfg]
    exact (disch_inv hrun.1 (ih (by omega)) hA (J k) le_rfl).1

theorem relabel_only_core (hrun : IsFIFORun N L K S J) (k : ℕ) (hk : k < K) (j : ℕ) (hj : j < J k)
    (hrel : IsRelabelOp N L (frontVertex N (S k))
      (prIter N L (frontVertex N (S k)) (S k).cfg j)) :
    RelabelApplicable N (prIter N L (frontVertex N (S k)) (S k).cfg j).f
      (prIter N L (frontVertex N (S k)) (S k).cfg j).d (frontVertex N (S k)) := by
  obtain ⟨i, rest, hQ, hJ, hA, hcfg⟩ := front_eq (hrun.2.2.2 k hk)
  have hI := (disch_inv hrun.1 (run_inv hrun k hk.le) hA j hj.le).1
  exact relabel_applicable hrun.1 hI (hA j hj).1 hrel

theorem label_core (hrun : IsFIFORun N L K S J) :
    (∀ k ≤ K, ∀ v, (S k).cfg.d v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)) ∧
    (∀ k < K, ∀ j ≤ J k, ∀ v,
      (prIter N L (frontVertex N (S k)) (S k).cfg j).d v
        ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)) := by
  refine ⟨fun k hk v => (run_inv hrun k hk).bound v, ?_⟩
  intro k hk j hj v
  obtain ⟨i, rest, hQ, hJ, hA, hcfg⟩ := front_eq (hrun.2.2.2 k hk)
  exact (disch_inv hrun.1 (run_inv hrun k hk.le) hA j hj).1.bound v


end Run

noncomputable def lab (σ : Config V) (x : V) : ℕ := (σ.d x).toNat

section Lab
variable {N : Network V} {L : V → List V}

lemma lab_cast {σ : Config V} (hI : Inv N L σ) (x : V) : σ.d x = (lab σ x : ℕ∞) :=
  (ENat.coe_toNat (hI.fin x)).symm

lemma lab_le {σ : Config V} (hI : Inv N L σ) (x : V) : lab σ x ≤ 2 * Fintype.card V - 1 := by
  have := hI.bound x; rw [lab_cast hI x] at this; exact_mod_cast this

lemma lab_mono {σ τ : Config V} (h1 : Inv N L σ) (h2 : Inv N L τ) {x : V}
    (h : σ.d x ≤ τ.d x) : lab σ x ≤ lab τ x := by
  rw [lab_cast h1 x, lab_cast h2 x] at h; exact_mod_cast h

lemma lab_lt {σ τ : Config V} (h1 : Inv N L σ) (h2 : Inv N L τ) {x : V}
    (h : σ.d x < τ.d x) : lab σ x < lab τ x := by
  rw [lab_cast h1 x, lab_cast h2 x] at h; exact_mod_cast h

lemma disch_count {v : V} {σ : Config V} {J : ℕ}
    (hL : IsEdgeList N L) (hI : Inv N L σ)
    (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j)) :
    ∀ j ≤ J, ((Finset.range j).filter (fun i => IsRelabelOp N L v (prIter N L v σ i))).card
      + lab σ v ≤ lab (prIter N L v σ j) v := by
  intro j
  induction j with
  | zero => intro _; simp [iter_zero]
  | succ j ih =>
    intro hj
    have h0 := ih (by omega)
    have hIj := (disch_inv hL hI hA j (by omega)).1
    have hst := step_inv hL hIj (hA j (by omega))
    have hIj1 : Inv N L (prIter N L v σ (j + 1)) := (disch_inv hL hI hA (j + 1) hj).1
    rw [iter_succ] at hIj1 ⊢
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with hP
    · rw [Finset.card_insert_of_notMem (by simp)]
      have := lab_lt hIj hIj1 (hst.2.2 hP)
      omega
    · have := lab_mono hIj hIj1 (hst.2.1 v)
      omega

end Lab

section Run2
variable {N : Network V} {L : V → List V} {K : ℕ} {S : ℕ → State V} {J : ℕ → ℕ}

lemma run_count (hrun : IsFIFORun N L K S J) (x : V) : ∀ k ≤ K,
    (∑ k' ∈ Finset.range k,
      if frontVertex N (S k') = x then
        ((Finset.range (J k')).filter
          (fun j => IsRelabelOp N L x (prIter N L x (S k').cfg j))).card
      else 0) + lab (S 0).cfg x ≤ lab (S k).cfg x := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h0 := ih (by omega)
    obtain ⟨i, rest, hQ, hJ, hA, hcfg⟩ := front_eq (hrun.2.2.2 k (by omega))
    have hIk := run_inv hrun k (by omega)
    have hIk1 := run_inv hrun (k + 1) hk
    rw [Finset.sum_range_succ]
    split_ifs with hfx
    · rw [hfx] at hA hcfg
      have := disch_count hrun.1 hIk hA (J k) le_rfl
      rw [← hcfg] at this
      omega
    · have := (disch_inv hrun.1 hIk hA (J k) le_rfl).2 x
      rw [← hcfg] at this
      have := lab_mono hIk hIk1 this
      omega

lemma front_active (hrun : IsFIFORun N L K S J) {k : ℕ} (hk : k < K) :
    IsActive N (S k).cfg.f (S k).cfg.d (frontVertex N (S k)) := by
  obtain ⟨i, rest, hQ, hJ, hA, hcfg⟩ := front_eq (hrun.2.2.2 k hk)
  exact (hA 0 hJ).1

lemma relabelAt_le (hrun : IsFIFORun N L K S J) (x : V) :
    relabelCountAt N L K S J x ≤ 2 * Fintype.card V - 1 := by
  have := run_count hrun x K le_rfl
  have := lab_le (run_inv hrun K le_rfl) x
  unfold relabelCountAt; omega

lemma relabelAt_zero (hrun : IsFIFORun N L K S J) (x : V) (hx : x = N.s ∨ x = N.t) :
    relabelCountAt N L K S J x = 0 := by
  unfold relabelCountAt
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  have ha := front_active hrun hk
  rw [if_neg]
  intro h; rw [h] at ha
  rcases hx with rfl | rfl
  · exact ha.1 rfl
  · exact ha.2.1 rfl

lemma card_inner (N : Network V) :
    (Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t)).card = Fintype.card V - 2 := by
  have : Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t) = ({N.s, N.t} : Finset V)ᶜ := by
    ext x; simp
  rw [this, Finset.card_compl, Finset.card_pair N.s_ne_t]

theorem relabel_count_core (hrun : IsFIFORun N L K S J) :
    (∀ x, relabelCountAt N L K S J x ≤ 2 * Fintype.card V - 1) ∧
    relabelCount N L K S J ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
    (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by
  refine ⟨fun x => relabelAt_le hrun x, ?_, ?_⟩
  · unfold relabelCount
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t)))]
    · calc _ ≤ ∑ v ∈ Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t), (2 * Fintype.card V - 1) :=
            Finset.sum_le_sum (fun v _ => relabelAt_le hrun v)
        _ = (2 * Fintype.card V - 1) * (Fintype.card V - 2) := by
            rw [Finset.sum_const, card_inner N, smul_eq_mul, mul_comm]
    · intro x _ hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hx
      exact relabelAt_zero hrun x hx
  · have h2 := card_two_le N
    obtain ⟨a, ha⟩ : ∃ a, Fintype.card V = a + 2 := ⟨Fintype.card V - 2, by omega⟩
    rw [ha]
    have e1 : 2 * (a + 2) - 1 = 2 * a + 3 := by omega
    have e2 : a + 2 - 2 = a := by omega
    rw [e1, e2]; nlinarith

end Run2

section Step2
variable {N : Network V} {L : V → List V}

lemma pr_cases {v : V} {σ : Config V} (hA : PRApplicable N L v σ) :
    ∃ w, (L v)[σ.cur v]? = some w ∧
      ((PushApplicable N σ.f σ.d v w ∧
          pushRelabel N L v σ = { σ with f := pushFlow N σ.f v w }) ∨
       (¬ PushApplicable N σ.f σ.d v w ∧
          pushRelabel N L v σ = { σ with cur := Function.update σ.cur v (σ.cur v + 1) }) ∨
       (¬ PushApplicable N σ.f σ.d v w ∧ IsRelabelOp N L v σ ∧ pushRelabel N L v σ =
          { σ with d := Function.update σ.d v (relabelLabel N σ.f σ.d v),
                   cur := Function.update σ.cur v 0 })) := by
  have hc := hA.2
  have hw := List.getElem?_eq_getElem hc
  refine ⟨_, hw, ?_⟩
  rw [pr_eq hw]
  split_ifs with hp hn
  · left; exact ⟨hp, rfl⟩
  · right; left; exact ⟨hp, rfl⟩
  · right; right; exact ⟨hp, ⟨_, hw, hp, by omega⟩, rfl⟩

lemma pr_d_other {v x : V} {σ : Config V} (hA : PRApplicable N L v σ) (hx : x ≠ v) :
    (pushRelabel N L v σ).d x = σ.d x := by
  obtain ⟨w, hw, ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩⟩ := pr_cases hA <;> rw [h]
  · exact Function.update_of_ne hx _ _

lemma pr_d_of_not_relabel {v : V} {σ : Config V} (hA : PRApplicable N L v σ)
    (hr : ¬ IsRelabelOp N L v σ) : (pushRelabel N L v σ).d = σ.d := by
  obtain ⟨w, hw, ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h1, h⟩⟩ := pr_cases hA <;> rw [h]
  exact absurd h1 hr

lemma pr_excess {v x : V} {σ : Config V} (hA : PRApplicable N L v σ) (hx : x ≠ v) :
    excess σ.f x ≤ excess (pushRelabel N L v σ).f x ∧
      (excess σ.f x < excess (pushRelabel N L v σ).f x →
        (L v)[σ.cur v]? = some x ∧ PushApplicable N σ.f σ.d v x) := by
  obtain ⟨w, hw, ⟨hp, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩⟩ := pr_cases hA <;> rw [h]
  · have hvw := push_ne hp
    by_cases hxw : x = w
    · subst hxw
      simp only
      rw [excess_push_w N σ.f v x hvw]
      have := (pushAmount_pos hp).le
      exact ⟨by linarith, fun _ => ⟨hw, hp⟩⟩
    · simp only
      rw [excess_push_other N σ.f v w x hvw hx hxw]
      exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  · exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩

lemma act_mono_other {v x : V} {σ : Config V} (hA : PRApplicable N L v σ) (hx : x ≠ v)
    (h : IsActive N σ.f σ.d x) :
    IsActive N (pushRelabel N L v σ).f (pushRelabel N L v σ).d x :=
  ⟨h.1, h.2.1, by rw [pr_d_other hA hx]; exact h.2.2.1,
    lt_of_lt_of_le h.2.2.2 (pr_excess hA hx).1⟩

lemma act_new_other {v x : V} {σ : Config V} (hA : PRApplicable N L v σ) (hx : x ≠ v)
    (h1 : ¬ IsActive N σ.f σ.d x)
    (h2 : IsActive N (pushRelabel N L v σ).f (pushRelabel N L v σ).d x) :
    (L v)[σ.cur v]? = some x ∧ PushApplicable N σ.f σ.d v x := by
  apply (pr_excess hA hx).2
  by_contra hle
  push_neg at hle
  apply h1
  exact ⟨h2.1, h2.2.1, by rw [← pr_d_other hA hx]; exact h2.2.2.1,
    lt_of_lt_of_le h2.2.2.2 hle⟩

lemma activated_of {v x : V} {σ : Config V} (hw : (L v)[σ.cur v]? = some x)
    (h1 : ¬ IsActive N σ.f σ.d x)
    (h2 : IsActive N (pushRelabel N L v σ).f (pushRelabel N L v σ).d x) :
    activated N L v σ = [x] := by
  unfold activated
  simp only [hw]
  rw [if_pos ⟨h1, h2⟩]

lemma mem_activated {v y : V} {σ : Config V} (h : y ∈ activated N L v σ) :
    (L v)[σ.cur v]? = some y ∧ ¬ IsActive N σ.f σ.d y ∧
      IsActive N (pushRelabel N L v σ).f (pushRelabel N L v σ).d y := by
  unfold activated at h
  split at h
  · simp at h
  · rename_i w hw
    split_ifs at h with hc
    · simp only [List.mem_singleton] at h
      subst h; exact ⟨hw, hc⟩
    · simp at h

lemma ne_of_L (hL : IsEdgeList N L) {v y : V} {i : ℕ} (h : (L v)[i]? = some y) : y ≠ v := by
  intro hyv; subst hyv
  have := List.mem_of_getElem? h
  rw [(hL y).2, N.c_self] at this; simp at this

noncomputable def Phi (N : Network V) (σ : Config V) : ℕ :=
  (Finset.univ.filter (fun x => IsActive N σ.f σ.d x)).sup (fun x => lab σ x + 1)

noncomputable def Lam (σ : Config V) : ℕ := ∑ x, lab σ x

lemma le_Phi {σ : Config V} {x : V} (h : IsActive N σ.f σ.d x) : lab σ x + 1 ≤ Phi N σ :=
  Finset.le_sup (f := fun x => lab σ x + 1) (by simp [h])

lemma lam_step (hL : IsEdgeList N L) {v : V} {σ : Config V} (hA : PRApplicable N L v σ) :
    Lam (pushRelabel N L v σ) + lab σ v = Lam σ + lab (pushRelabel N L v σ) v := by
  unfold Lam
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  have : ∑ x ∈ Finset.univ.erase v, lab (pushRelabel N L v σ) x =
      ∑ x ∈ Finset.univ.erase v, lab σ x :=
    Finset.sum_congr rfl (fun x hx => by unfold lab; rw [pr_d_other hA (Finset.ne_of_mem_erase hx)])
  omega

lemma lab_step_mono (hL : IsEdgeList N L) {v : V} {σ : Config V} (hI : Inv N L σ)
    (hA : PRApplicable N L v σ) (x : V) : lab σ x ≤ lab (pushRelabel N L v σ) x :=
  lab_mono hI (step_inv hL hI hA).1 ((step_inv hL hI hA).2.1 x)

lemma lam_mono (hL : IsEdgeList N L) {v : V} {σ : Config V} (hI : Inv N L σ)
    (hA : PRApplicable N L v σ) : Lam σ ≤ Lam (pushRelabel N L v σ) := by
  have := lam_step hL hA; have := lab_step_mono hL hI hA v; omega

lemma lam_strict (hL : IsEdgeList N L) {v : V} {σ : Config V} (hI : Inv N L σ)
    (hA : PRApplicable N L v σ) (hr : IsRelabelOp N L v σ) :
    Lam σ < Lam (pushRelabel N L v σ) := by
  have := lam_step hL hA
  have := lab_lt hI (step_inv hL hI hA).1 ((step_inv hL hI hA).2.2 hr); omega

lemma phi_step (hL : IsEdgeList N L) {v : V} {σ : Config V} (hI : Inv N L σ)
    (hA : PRApplicable N L v σ) :
    Phi N (pushRelabel N L v σ) + Lam σ ≤ Phi N σ + Lam (pushRelabel N L v σ) := by
  have hls := lam_step hL hA
  have hmv := lab_step_mono hL hI hA v
  have hI' := (step_inv hL hI hA).1
  have hv := le_Phi (N := N) hA.1
  have key : ∀ x ∈ Finset.univ.filter (fun x => IsActive N (pushRelabel N L v σ).f
      (pushRelabel N L v σ).d x), lab (pushRelabel N L v σ) x + 1 + Lam σ ≤
        Phi N σ + Lam (pushRelabel N L v σ) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    by_cases hxv : x = v
    · subst hxv; omega
    · have hlx : lab (pushRelabel N L v σ) x = lab σ x := by
        unfold lab; rw [pr_d_other hA hxv]
      by_cases hax : IsActive N σ.f σ.d x
      · have := le_Phi (N := N) hax; omega
      · obtain ⟨_, hp⟩ := act_new_other hA hxv hax hx
        have h3 := hp.2.2
        rw [lab_cast hI v, lab_cast hI x] at h3
        have : lab σ v = lab σ x + 1 := by exact_mod_cast h3
        omega
  have : Phi N (pushRelabel N L v σ) ≤ Phi N σ + Lam (pushRelabel N L v σ) - Lam σ := by
    apply Finset.sup_le
    intro x hx; have := key x hx; omega
  omega

end Step2

section Disch
variable {N : Network V} {L : V → List V} {v : V} {σ : Config V} {J : ℕ}

lemma d_phi (hL : IsEdgeList N L) (hI : Inv N L σ)
    (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j)) :
    ∀ j ≤ J, Phi N (prIter N L v σ j) + Lam σ ≤ Phi N σ + Lam (prIter N L v σ j) := by
  intro j
  induction j with
  | zero => intro _; simp [iter_zero]
  | succ j ih =>
    intro hj
    have h0 := ih (by omega)
    have hIj := (disch_inv hL hI hA j (by omega)).1
    have := phi_step hL hIj (hA j (by omega))
    rw [iter_succ]; omega

lemma d_lam_mono (hL : IsEdgeList N L) (hI : Inv N L σ)
    (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j)) :
    ∀ j j', j ≤ j' → j' ≤ J → Lam (prIter N L v σ j) ≤ Lam (prIter N L v σ j') := by
  intro j j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j' hjj' ih =>
    intro hj'
    have hIj := (disch_inv hL hI hA j' (by omega)).1
    have := lam_mono hL hIj (hA j' (by omega))
    rw [iter_succ]; exact (ih (by omega)).trans this

lemma d_norelabel (hL : IsEdgeList N L) (hI : Inv N L σ)
    (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j))
    (heq : Lam (prIter N L v σ J) = Lam σ) :
    ∀ j ≤ J, (prIter N L v σ j).d = σ.d := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hIj := (disch_inv hL hI hA j (by omega)).1
    have hnr : ¬ IsRelabelOp N L v (prIter N L v σ j) := by
      intro hr
      have h1 := lam_strict hL hIj (hA j (by omega)) hr
      have h2 := d_lam_mono hL hI hA 0 j (by omega) (by omega)
      have h3 := d_lam_mono hL hI hA (j + 1) J hj le_rfl
      rw [iter_succ] at h3
      simp only [iter_zero] at h2
      omega
    rw [iter_succ, pr_d_of_not_relabel (hA j (by omega)) hnr]; exact ih (by omega)

lemma d_other (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j)) {x : V} (hx : x ≠ v) :
    ∀ j ≤ J, (prIter N L v σ j).d x = σ.d x := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [iter_succ, pr_d_other (hA j (by omega)) hx]; exact ih (by omega)

lemma d_act_mono (hA : ∀ j < J, PRApplicable N L v (prIter N L v σ j)) {x : V} (hx : x ≠ v)
    (j : ℕ) (h : IsActive N (prIter N L v σ j).f (prIter N L v σ j).d x) :
    ∀ j', j ≤ j' → j' ≤ J → IsActive N (prIter N L v σ j').f (prIter N L v σ j').d x := by
  intro j' hjj'
  induction j', hjj' using Nat.le_induction with
  | base => intro _; exact h
  | succ j' hjj' ih =>
    intro hj'
    rw [iter_succ]; exact act_mono_other (hA j' (by omega)) hx (ih (by omega))

lemma d_ivt {x : V} (h0 : ¬ IsActive N σ.f σ.d x) :
    ∀ j, IsActive N (prIter N L v σ j).f (prIter N L v σ j).d x →
      ∃ j' < j, ¬ IsActive N (prIter N L v σ j').f (prIter N L v σ j').d x ∧
        IsActive N (prIter N L v σ (j' + 1)).f (prIter N L v σ (j' + 1)).d x := by
  intro j
  induction j with
  | zero => intro h; exact absurd h h0
  | succ j ih =>
    intro h
    by_cases hj : IsActive N (prIter N L v σ j).f (prIter N L v σ j).d x
    · obtain ⟨j', hj', h1, h2⟩ := ih hj; exact ⟨j', by omega, h1, h2⟩
    · exact ⟨j, by omega, hj, h⟩

end Disch

section Queue
variable {N : Network V} {L : V → List V} {K : ℕ} {S : ℕ → State V} {J : ℕ → ℕ}

lemma disch_all {S0 S1 : State V} {J0 : ℕ} (h : DischargeStep N L S0 J0 S1) :
    ∃ i rest, S0.Q = (frontVertex N S0, i) :: rest ∧ 0 < J0 ∧
      (∀ j < J0, PRApplicable N L (frontVertex N S0) (prIter N L (frontVertex N S0) S0.cfg j)) ∧
      (∀ j, 1 ≤ j → j < J0 → ¬ DischargeStop (frontVertex N S0) S0.cfg
          (prIter N L (frontVertex N S0) S0.cfg j)) ∧
      DischargeStop (frontVertex N S0) S0.cfg (prIter N L (frontVertex N S0) S0.cfg J0) ∧
      S1.cfg = prIter N L (frontVertex N S0) S0.cfg J0 ∧
      S1.Q = rest
      ++ (List.range J0).flatMap
          (fun j => (activated N L (frontVertex N S0)
            (prIter N L (frontVertex N S0) S0.cfg j)).map (fun w => (w, i + 1)))
      ++ (if IsActive N (prIter N L (frontVertex N S0) S0.cfg J0).f
            (prIter N L (frontVertex N S0) S0.cfg J0).d (frontVertex N S0)
          then [(frontVertex N S0, i + 1)] else []) := by
  obtain ⟨v, i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := h
  have hf : frontVertex N S0 = v := by simp [frontVertex, hQ]
  rw [hf]; exact ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩

def TagInv (Q : List (V × ℕ)) : Prop :=
  Q.Pairwise (fun a b => a.2 ≤ b.2) ∧ ∀ a ∈ Q, ∀ b ∈ Q, b.2 ≤ a.2 + 1

lemma pairwise_const (l : List (V × ℕ)) (c : ℕ) (h : ∀ e ∈ l, e.2 = c) :
    l.Pairwise (fun a b => a.2 ≤ b.2) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons]
    refine ⟨fun b hb => ?_, ih (fun e he => h e (List.mem_cons_of_mem _ he))⟩
    rw [h a List.mem_cons_self, h b (List.mem_cons_of_mem _ hb)]

lemma tag_step {v : V} {i : ℕ} {rest A : List (V × ℕ)} (hT : TagInv ((v, i) :: rest))
    (hA : ∀ e ∈ A, e.2 = i + 1) :
    TagInv (rest ++ A) ∧ ∀ e ∈ rest ++ A, i ≤ e.2 ∧ e.2 ≤ i + 1 := by
  obtain ⟨hp, hw⟩ := hT
  rw [List.pairwise_cons] at hp
  have hr : ∀ e ∈ rest, i ≤ e.2 ∧ e.2 ≤ i + 1 := fun e he =>
    ⟨hp.1 e he, hw (v, i) List.mem_cons_self e (List.mem_cons_of_mem _ he)⟩
  have hall : ∀ e ∈ rest ++ A, i ≤ e.2 ∧ e.2 ≤ i + 1 := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hr e h
    · rw [hA e h]; omega
  refine ⟨⟨?_, ?_⟩, hall⟩
  · rw [List.pairwise_append]
    refine ⟨hp.2, pairwise_const A (i + 1) hA, fun a ha b hb => ?_⟩
    rw [hA b hb]; exact (hr a ha).2
  · intro a ha b hb
    rcases List.mem_append.mp ha with h1 | h1 <;> rcases List.mem_append.mp hb with h2 | h2
    · exact hw _ (List.mem_cons_of_mem _ h1) _ (List.mem_cons_of_mem _ h2)
    · rw [hA b h2]; have := (hr a h1).1; omega
    · rw [hA a h1]; have := (hr b h2).2; omega
    · rw [hA a h1, hA b h2]; omega

def QInv (N : Network V) (S : State V) : Prop :=
  (∀ x, IsActive N S.cfg.f S.cfg.d x → x ∈ S.Q.map Prod.fst) ∧ TagInv S.Q

lemma init_qinv (hrun : IsFIFORun N L K S J) : QInv N (S 0) := by
  obtain ⟨hL, hcfg, ⟨hnd, hmem, htag⟩, _⟩ := hrun
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · rw [hmem]
    refine ⟨hx.1, hx.2.1, ?_⟩
    have := hx.2.2.2
    rw [hcfg] at this
    unfold excess at this
    simp only [initConfig, initFlow] at this
    rw [Finset.sum_eq_single N.s] at this
    · simpa using this
    · intro b _ hb; simp [hb, hx.1]
    · simp
  · apply pairwise_const _ 1 htag
  · intro a ha b hb; rw [htag a ha, htag b hb]; omega

lemma mem_Q' {S0 S1 : State V} {J0 i : ℕ} {rest : List (V × ℕ)} {v : V}
    (hQ' : S1.Q = rest
      ++ (List.range J0).flatMap
          (fun j => (activated N L v (prIter N L v S0.cfg j)).map (fun w => (w, i + 1)))
      ++ (if IsActive N (prIter N L v S0.cfg J0).f (prIter N L v S0.cfg J0).d v
          then [(v, i + 1)] else [])) :
    (∀ e ∈ S1.Q, e ∈ rest ∨ e.2 = i + 1) ∧ (∀ e ∈ rest, e ∈ S1.Q) ∧
    (∀ j < J0, ∀ x ∈ activated N L v (prIter N L v S0.cfg j), (x, i + 1) ∈ S1.Q) ∧
    (IsActive N (prIter N L v S0.cfg J0).f (prIter N L v S0.cfg J0).d v → (v, i + 1) ∈ S1.Q) := by
  rw [hQ']
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at he
    rcases he with (h | ⟨j, _, x, _, rfl⟩) | h
    · exact Or.inl h
    · exact Or.inr rfl
    · split_ifs at h
      · simp only [List.mem_singleton] at h; subst h; exact Or.inr rfl
      · simp at h
  · intro e he; simp [he]
  · intro j hj x hx
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inr ⟨j, hj, x, hx, rfl⟩)
  · intro h; simp [h]


lemma tags_new {v : V} {i : ℕ} (A : List V)
    (Y : List (V × ℕ)) (hY : ∀ e ∈ Y, e.2 = i + 1) (J0 : ℕ) (F : ℕ → List V) :
    ∀ e ∈ (List.range J0).flatMap (fun j => (F j).map (fun w => (w, i + 1))) ++ Y, e.2 = i + 1 := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · simp only [List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨j, _, x, _, rfl⟩ := h; rfl
  · exact hY e h

lemma qstep {S0 S1 : State V} {J0 i : ℕ} {rest : List (V × ℕ)} {v : V}
    (hT : TagInv ((v, i) :: rest))
    (hQ' : S1.Q = rest
      ++ (List.range J0).flatMap
          (fun j => (activated N L v (prIter N L v S0.cfg j)).map (fun w => (w, i + 1)))
      ++ (if IsActive N (prIter N L v S0.cfg J0).f (prIter N L v S0.cfg J0).d v
          then [(v, i + 1)] else [])) :
    TagInv S1.Q ∧ ∀ e ∈ S1.Q, i ≤ e.2 ∧ e.2 ≤ i + 1 := by
  rw [hQ', List.append_assoc]
  apply tag_step hT
  apply tags_new (v := v) [] _ _ J0
  intro e he
  split_ifs at he
  · simp only [List.mem_singleton] at he; subst he; rfl
  · simp at he

end Queue

section Run3
variable {N : Network V} {L : V → List V} {K : ℕ} {S : ℕ → State V} {J : ℕ → ℕ}

lemma qinv_run (hrun : IsFIFORun N L K S J) : ∀ k ≤ K, QInv N (S k) := by
  intro k
  induction k with
  | zero => intro _; exact init_qinv hrun
  | succ k ih =>
    intro hk
    have hq := ih (by omega)
    obtain ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := disch_all (hrun.2.2.2 k (by omega))
    have hT : TagInv ((frontVertex N (S k), i) :: rest) := hQ ▸ hq.2
    refine ⟨?_, (qstep hT hQ').1⟩
    have hm := mem_Q' hQ'
    intro x hx
    rw [hcfg] at hx
    by_cases hxv : x = frontVertex N (S k)
    · subst hxv
      exact List.mem_map.mpr ⟨_, hm.2.2.2 hx, rfl⟩
    · by_cases h0 : IsActive N (S k).cfg.f (S k).cfg.d x
      · have := hq.1 x h0
        rw [hQ] at this
        simp only [List.map_cons, List.mem_cons] at this
        rcases this with h | h
        · exact absurd h hxv
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
          exact List.mem_map.mpr ⟨e, hm.2.1 e he, rfl⟩
      · obtain ⟨j', hj', h1, h2⟩ := d_ivt (L := L) (v := frontVertex N (S k)) h0 (J k) hx
        rw [iter_succ] at h2
        have ha := act_new_other (hA j' (by omega)) hxv h1 h2
        have hact := activated_of ha.1 h1 h2
        have := hm.2.2.1 j' hj' x (by rw [hact]; exact List.mem_singleton_self x)
        exact List.mem_map.mpr ⟨_, this, rfl⟩

lemma lam_le {σ : Config V} (hI : Inv N L σ) : Lam σ ≤ Fintype.card V + (Fintype.card V - 1) * (2 * Fintype.card V - 1) := by
  unfold Lam
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ N.s)]
  have h1 : lab σ N.s = Fintype.card V := by unfold lab; rw [hI.ds]; simp
  have h2 : ∑ x ∈ Finset.univ.erase N.s, lab σ x ≤ (Finset.univ.erase N.s).card • (2 * Fintype.card V - 1) :=
    Finset.sum_le_card_nsmul _ _ _ (fun x _ => lab_le hI x)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), smul_eq_mul, Finset.card_univ] at h2
  omega

lemma lam_ge {σ : Config V} (hI : Inv N L σ) : Fintype.card V ≤ Lam σ := by
  unfold Lam
  have h1 : lab σ N.s = Fintype.card V := by unfold lab; rw [hI.ds]; simp
  rw [← h1]
  exact Finset.single_le_sum (f := fun x => lab σ x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)

lemma phi_init (hrun : IsFIFORun N L K S J) : Phi N (S 0).cfg ≤ 1 := by
  apply Finset.sup_le
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have : lab (S 0).cfg x = 0 := by
    unfold lab; rw [hrun.2.1]; simp [initConfig, initLabel, hx.1]
  omega

def PassInv (N : Network V) (S : ℕ → State V) (k : ℕ) : Prop :=
  ∃ B lam, (frontPass (S k) - 1) + B + 2 * Lam (S 0).cfg ≤ Phi N (S 0).cfg + 2 * lam ∧
    lam ≤ Lam (S k).cfg ∧ Phi N (S k).cfg + lam ≤ B + Lam (S k).cfg ∧
    (Lam (S k).cfg = lam → ∀ x, IsActive N (S k).cfg.f (S k).cfg.d x →
      (∀ e ∈ (S k).Q, e.1 = x → e.2 ≠ frontPass (S k)) → lab (S k).cfg x + 2 ≤ B)

lemma pass_inv (hrun : IsFIFORun N L K S J) : ∀ k < K, PassInv N S k := by
  intro k
  induction k with
  | zero =>
    intro hK
    obtain ⟨i, rest, hQ, _⟩ := disch_all (hrun.2.2.2 0 hK)
    have hi : i = 1 := hrun.2.2.1.2.2 _ (by rw [hQ]; exact List.mem_cons_self)
    have hfp : frontPass (S 0) = 1 := by simp [frontPass, hQ, hi]
    refine ⟨Phi N (S 0).cfg, Lam (S 0).cfg, by rw [hfp]; omega, le_rfl, le_refl _, ?_⟩
    intro _ x hx hno
    exfalso
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ((init_qinv hrun).1 x hx)
    exact hno e he rfl (by rw [hfp]; exact hrun.2.2.1.2.2 e he)
  | succ k ih =>
    intro hK
    obtain ⟨B, lam, h1, h2, h3, h4⟩ := ih (by omega)
    have hL := hrun.1
    obtain ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := disch_all (hrun.2.2.2 k (by omega))
    set v := frontVertex N (S k) with hv
    have hfp : frontPass (S k) = i := by simp [frontPass, hQ]
    rw [hfp] at h1 h4
    have hI0 := run_inv hrun k (by omega)
    have hphi := d_phi hL hI0 hA (J k) le_rfl
    have hlam := d_lam_mono hL hI0 hA 0 (J k) (by omega) le_rfl
    simp only [iter_zero] at hlam
    rw [← hcfg] at hphi hlam
    have hI1 := run_inv hrun (k + 1) (by omega)
    have hq0 := qinv_run hrun k (by omega)
    have hq1 := qinv_run hrun (k + 1) (by omega)
    have hT : TagInv ((v, i) :: rest) := hQ ▸ hq0.2
    have hqs := (qstep hT hQ').2
    have hm := mem_Q' hQ'
    -- Fact F
    have hF : Lam (S (k + 1)).cfg = lam → ∀ x, IsActive N (S (k + 1)).cfg.f (S (k + 1)).cfg.d x →
        (∀ e ∈ (S (k + 1)).Q, e.1 = x → e.2 ≠ i) → lab (S (k + 1)).cfg x + 2 ≤ B := by
      intro heq x hx hno
      have hl0 : Lam (S k).cfg = lam := by omega
      have hd := d_norelabel hL hI0 hA (by rw [← hcfg]; omega)
      have hdJ : (S (k + 1)).cfg.d = (S k).cfg.d := by rw [hcfg]; exact hd (J k) le_rfl
      have hlab : ∀ y, lab (S (k + 1)).cfg y = lab (S k).cfg y := by
        intro y; unfold lab; rw [hdJ]
      have hxv : x ≠ v := by
        intro hxv
        rcases hst with h | h
        · rw [← hcfg, ← hxv] at h; have := hx.2.2.2; linarith
        · rw [← hcfg, hdJ] at h; exact lt_irrefl _ h
      rw [hlab]
      by_cases h0 : IsActive N (S k).cfg.f (S k).cfg.d x
      · apply h4 hl0 x h0
        intro e he hex
        rw [hQ] at he
        rcases List.mem_cons.mp he with h | h
        · subst h; exact absurd hex.symm hxv
        · exact hno e (hm.2.1 e h) hex
      · rw [hcfg] at hx
        obtain ⟨j', hj', ha1, ha2⟩ := d_ivt (L := L) (v := v) h0 (J k) hx
        rw [iter_succ] at ha2
        have hp := (act_new_other (hA j' (by omega)) hxv ha1 ha2).2
        have h5 := hp.2.2
        rw [hd j' (by omega)] at h5
        rw [lab_cast hI0 v, lab_cast hI0 x] at h5
        have h6 : lab (S k).cfg v = lab (S k).cfg x + 1 := by exact_mod_cast h5
        have h7 := le_Phi (N := N) (hA 0 hJ).1
        simp only [iter_zero] at h7
        omega
    -- next front
    obtain ⟨i', rest', hQ1, hJ1, hA1, _⟩ := disch_all (hrun.2.2.2 (k + 1) hK)
    have hfp1 : frontPass (S (k + 1)) = i' := by simp [frontPass, hQ1]
    have hi' := hqs _ (by rw [hQ1]; exact List.mem_cons_self)
    simp only at hi'
    unfold PassInv
    rw [hfp1]
    rcases (show i' = i ∨ i' = i + 1 by omega) with he | he
    · rw [he]
      refine ⟨B, lam, h1, by omega, by omega, hF⟩
    · rw [he]
      have hall : ∀ e ∈ (S (k + 1)).Q, e.2 = i + 1 := by
        intro e hmem
        have := (hqs e hmem).2
        have hpw := hq1.2.1
        rw [hQ1, List.pairwise_cons] at hpw
        rw [hQ1] at hmem
        rcases List.mem_cons.mp hmem with h | h
        · rw [h]; omega
        · have := hpw.1 e h; omega
      refine ⟨Phi N (S (k + 1)).cfg, Lam (S (k + 1)).cfg, ?_, le_rfl, le_refl _, ?_⟩
      · by_cases hc : Lam (S (k + 1)).cfg = lam
        · have hfa := (hA1 0 hJ1).1
          simp only [iter_zero] at hfa
          have hno : ∀ x, IsActive N (S (k + 1)).cfg.f (S (k + 1)).cfg.d x →
              lab (S (k + 1)).cfg x + 2 ≤ B := by
            intro x hx
            apply hF hc x hx
            intro e he _
            rw [hall e he]; omega
          have hB := hno _ hfa
          have : Phi N (S (k + 1)).cfg ≤ B - 1 := by
            apply Finset.sup_le
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            have := hno x hx; omega
          omega
        · omega
      · intro _ x hx hno
        exfalso
        obtain ⟨e, hmem, rfl⟩ := List.mem_map.mp (hq1.1 x hx)
        exact hno e hmem rfl (hall e hmem)

theorem pass_core (hrun : IsFIFORun N L K S J) : passCount K S ≤ 4 * Fintype.card V ^ 2 := by
  unfold passCount
  apply Finset.sup_le
  intro k hk
  rw [Finset.mem_range] at hk
  obtain ⟨B, lam, h1, h2, h3, h4⟩ := pass_inv hrun k hk
  have hI := run_inv hrun k hk.le
  have hI0 := run_inv hrun 0 (by omega)
  have a1 := lam_le hI
  have a2 := lam_ge hI0
  have a3 := phi_init hrun
  have hn := card_two_le N
  have key : 2 + 2 * ((Fintype.card V - 1) * (2 * Fintype.card V - 1)) ≤ 4 * Fintype.card V ^ 2 := by
    obtain ⟨a, ha⟩ : ∃ a, Fintype.card V = a + 2 := ⟨Fintype.card V - 2, by omega⟩
    rw [ha]
    have e1 : 2 * (a + 2) - 1 = 2 * a + 3 := by omega
    have e2 : a + 2 - 1 = a + 1 := by omega
    rw [e1, e2]; nlinarith
  obtain ⟨m, hm⟩ : ∃ m, (Fintype.card V - 1) * (2 * Fintype.card V - 1) = m := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, 4 * Fintype.card V ^ 2 = q := ⟨_, rfl⟩
  rw [hm] at a1 key
  rw [hq] at key ⊢
  omega


def QInv2 (N : Network V) (S : State V) : Prop :=
  (S.Q.map Prod.fst).Nodup ∧ ∀ x ∈ S.Q.map Prod.fst, IsActive N S.cfg.f S.cfg.d x

lemma qinv2_run (hrun : IsFIFORun N L K S J) : ∀ k ≤ K, QInv2 N (S k) := by
  intro k
  induction k with
  | zero =>
    intro _
    obtain ⟨hL, hcfg, ⟨hnd, hmem, htag⟩, _⟩ := hrun
    refine ⟨hnd, fun x hx => ?_⟩
    rw [hmem] at hx
    refine ⟨hx.1, hx.2.1, ?_, ?_⟩
    · rw [hcfg]; simp [initConfig, initLabel, hx.1]
    · rw [hcfg]; unfold excess; simp only [initConfig, initFlow]
      rw [Finset.sum_eq_single N.s]
      · simpa using hx.2.2
      · intro b _ hb; simp [hb, hx.1]
      · simp
  | succ k ih =>
    intro hk
    have hq := ih (by omega)
    have hL := hrun.1
    obtain ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := disch_all (hrun.2.2.2 k (by omega))
    set v := frontVertex N (S k) with hv
    unfold QInv2 at hq ⊢
    rw [hQ] at hq
    obtain ⟨hnd, hact⟩ := hq
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at hnd hact
    have hrestact : ∀ x ∈ rest.map Prod.fst, x ≠ v ∧ ∀ j ≤ J k,
        IsActive N (prIter N L v (S k).cfg j).f (prIter N L v (S k).cfg j).d x := by
      intro x hx
      have hxv : x ≠ v := fun h => hnd.1 (h ▸ hx)
      exact ⟨hxv, fun j hj => d_act_mono hA hxv 0 (hact x (Or.inr hx)) j (by omega) hj⟩
    have hactd : ∀ j < J k, ∀ x ∈ activated N L v (prIter N L v (S k).cfg j),
        x ≠ v ∧ ¬ IsActive N (prIter N L v (S k).cfg j).f (prIter N L v (S k).cfg j).d x ∧
        ∀ j', j + 1 ≤ j' → j' ≤ J k →
          IsActive N (prIter N L v (S k).cfg j').f (prIter N L v (S k).cfg j').d x := by
      intro j hj x hx
      obtain ⟨h1, h2, h3⟩ := mem_activated hx
      have hxv : x ≠ v := ne_of_L hL h1
      rw [← iter_succ] at h3
      exact ⟨hxv, h2, fun j' h1' h2' => d_act_mono hA hxv (j + 1) h3 j' h1' h2'⟩
    rw [hQ', hcfg]
    simp only [List.map_append, List.map_flatMap, List.map_map]
    have hfm : (Prod.fst ∘ fun w : V => (w, i + 1)) = id := rfl
    simp only [hfm, List.map_id, apply_ite (List.map Prod.fst), List.map_cons, List.map_nil]
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨hnd.2, ?_, ?_⟩, ?_, ?_⟩
      · rw [List.nodup_flatMap]
        refine ⟨fun j _ => ?_, ?_⟩
        · unfold activated; split
          · simp
          · split_ifs <;> simp
        · apply List.Nodup.pairwise_of_forall_ne List.nodup_range
          intro a ha b hb hab
          rw [List.mem_range] at ha hb
          rw [Function.onFun, List.disjoint_left]
          intro x hxa hxb
          obtain ⟨_, hna, hfa⟩ := hactd a ha x hxa
          obtain ⟨_, hnb, hfb⟩ := hactd b hb x hxb
          rcases lt_or_gt_of_ne hab with h | h
          · exact hnb (hfa b (by omega) hb.le)
          · exact hna (hfb a (by omega) ha.le)
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
        rw [List.mem_range] at hj
        exact (hactd j hj x hy).2.1 ((hrestact x hx).2 j hj.le)
      · split_ifs <;> simp
      · intro x hx y hy hxy
        split_ifs at hy
        · simp only [List.mem_singleton] at hy
          rw [hxy, hy] at hx
          rcases List.mem_append.mp hx with h | h
          · exact (hrestact v h).1 rfl
          · obtain ⟨j, hj, hy'⟩ := List.mem_flatMap.mp h
            rw [List.mem_range] at hj
            exact (hactd j hj v hy').1 rfl
        · simp at hy
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · rcases List.mem_append.mp h with h | h
        · exact (hrestact x h).2 (J k) le_rfl
        · obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp h
          rw [List.mem_range] at hj
          exact (hactd j hj x hy).2.2 (J k) (by omega) le_rfl
      · split_ifs at h with hc
        · simp only [List.mem_singleton] at h; subst h; exact hc
        · simp at h

lemma qlen (hrun : IsFIFORun N L K S J) {k : ℕ} (hk : k ≤ K) :
    (S k).Q.length ≤ Fintype.card V := by
  have := (qinv2_run hrun k hk).1.length_le_card
  simpa using this

lemma front_mono (hrun : IsFIFORun N L K S J) {k' k : ℕ} (hkk : k' ≤ k) (hk : k < K) :
    frontPass (S k') ≤ frontPass (S k) := by
  induction k, hkk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hkk ih =>
    refine (ih (by omega)).trans ?_
    obtain ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := disch_all (hrun.2.2.2 k (by omega))
    have hq0 := qinv_run hrun k (by omega)
    have hT : TagInv ((frontVertex N (S k), i) :: rest) := hQ ▸ hq0.2
    have hqs := (qstep hT hQ').2
    obtain ⟨i', rest', hQ1, _⟩ := disch_all (hrun.2.2.2 (k + 1) hk)
    have := (hqs _ (by rw [hQ1]; exact List.mem_cons_self)).1
    simp [frontPass, hQ, hQ1]; exact this

lemma front_ge (hrun : IsFIFORun N L K S J) {k : ℕ} (hk : k < K) : 1 ≤ frontPass (S k) := by
  refine le_trans ?_ (front_mono hrun (Nat.zero_le k) hk)
  obtain ⟨i, rest, hQ, _⟩ := disch_all (hrun.2.2.2 0 (by omega))
  have hi : i = 1 := hrun.2.2.1.2.2 _ (by rw [hQ]; exact List.mem_cons_self)
  simp [frontPass, hQ, hi]

lemma tag_count (hrun : IsFIFORun N L K S J) (p : ℕ) : ∀ k ≤ K,
    ((Finset.range k).filter (fun k' => frontPass (S k') = p)).card
      + (S k).Q.countP (fun e => e.2 = p) ≤ Fintype.card V := by
  intro k
  induction k with
  | zero => intro _; simp only [Finset.range_zero, Finset.filter_empty, Finset.card_empty, zero_add]
            exact (List.countP_le_length).trans (qlen hrun (Nat.zero_le _))
  | succ k ih =>
    intro hk
    have h0 := ih (by omega)
    obtain ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := disch_all (hrun.2.2.2 k (by omega))
    have hfp : frontPass (S k) = i := by simp [frontPass, hQ]
    have hnew : ∀ e ∈ (List.range (J k)).flatMap
          (fun j => (activated N L (frontVertex N (S k))
            (prIter N L (frontVertex N (S k)) (S k).cfg j)).map (fun w => (w, i + 1)))
        ++ (if IsActive N (prIter N L (frontVertex N (S k)) (S k).cfg (J k)).f
              (prIter N L (frontVertex N (S k)) (S k).cfg (J k)).d (frontVertex N (S k))
            then [(frontVertex N (S k), i + 1)] else []), e.2 = i + 1 := by
      apply tags_new (v := frontVertex N (S k)) [] _ _ (J k)
      intro e he
      split_ifs at he
      · simp only [List.mem_singleton] at he; subst he; rfl
      · simp at he
    have hlen := qlen hrun hk
    rw [hQ] at h0
    rw [hQ', List.append_assoc] at hlen
    rw [hQ', List.append_assoc, List.countP_append]
    rw [List.countP_cons] at h0
    rw [Finset.range_add_one, Finset.filter_insert, hfp]
    by_cases hip : i + 1 = p
    · have hz : ((Finset.range k).filter (fun k' => frontPass (S k') = p)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k' hk'
        rw [Finset.mem_range] at hk'
        have := front_mono hrun hk'.le (by omega : k < K)
        omega
      rw [if_neg (by omega), hz, zero_add]
      have := List.countP_le_length (p := fun e : V × ℕ => decide (e.2 = p))
        (l := rest ++ ((List.range (J k)).flatMap
          (fun j => (activated N L (frontVertex N (S k))
            (prIter N L (frontVertex N (S k)) (S k).cfg j)).map (fun w => (w, i + 1)))
        ++ (if IsActive N (prIter N L (frontVertex N (S k)) (S k).cfg (J k)).f
              (prIter N L (frontVertex N (S k)) (S k).cfg (J k)).d (frontVertex N (S k))
            then [(frontVertex N (S k), i + 1)] else [])))
      rw [List.countP_append] at this
      omega
    · have hz : List.countP (fun e : V × ℕ => decide (e.2 = p))
          ((List.range (J k)).flatMap
          (fun j => (activated N L (frontVertex N (S k))
            (prIter N L (frontVertex N (S k)) (S k).cfg j)).map (fun w => (w, i + 1)))
        ++ (if IsActive N (prIter N L (frontVertex N (S k)) (S k).cfg (J k)).f
              (prIter N L (frontVertex N (S k)) (S k).cfg (J k)).d (frontVertex N (S k))
            then [(frontVertex N (S k), i + 1)] else [])) = 0 := by
        rw [List.countP_eq_zero]
        intro e he; rw [hnew e he]; simpa using hip
      rw [hz]
      by_cases hi : i = p
      · subst hi
        rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
        simp at h0; omega
      · rw [if_neg hi]
        simp [hi] at h0; omega

lemma nonsat_zero {v w : V} {σ : Config V} (hw : (L v)[σ.cur v]? = some w)
    (hp : PushApplicable N σ.f σ.d v w) (hr : 0 < residual N (pushFlow N σ.f v w) v w) :
    excess (pushRelabel N L v σ).f v = 0 := by
  rw [pr_eq hw, if_pos hp]
  have hvw := push_ne hp
  simp only
  rw [excess_push_v N σ.f v w hvw]
  rw [res_push_vw N σ.f v w hvw] at hr
  unfold pushAmount at hr ⊢
  rcases le_total (excess σ.f v) (residual N σ.f v w) with h | h
  · rw [min_eq_left h]; ring
  · rw [min_eq_right h] at hr; linarith

lemma nonsat_disch (hrun : IsFIFORun N L K S J) {k : ℕ} (hk : k < K) :
    ((Finset.range (J k)).filter
      (fun j => IsNonsatPush N L (frontVertex N (S k))
        (prIter N L (frontVertex N (S k)) (S k).cfg j))).card ≤ 1 := by
  obtain ⟨i, rest, hQ, hJ, hA, hns, hst, hcfg, hQ'⟩ := disch_all (hrun.2.2.2 k hk)
  have key : ∀ j ∈ (Finset.range (J k)).filter
      (fun j => IsNonsatPush N L (frontVertex N (S k))
        (prIter N L (frontVertex N (S k)) (S k).cfg j)), j + 1 = J k := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjJ, w, hw, hp, hr⟩ := hj
    have h0 := nonsat_zero hw hp hr
    rw [← iter_succ] at h0
    by_contra hne
    exact hns (j + 1) (by omega) (by omega) (Or.inl h0)
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have := key a ha; have := key b hb; omega

theorem goal_core (hrun : IsFIFORun N L K S J) :
    nonsatPushCount N L K S J ≤ 4 * Fintype.card V ^ 3 := by
  have h1 : nonsatPushCount N L K S J ≤ K := by
    unfold nonsatPushCount
    calc _ ≤ ∑ k ∈ Finset.range K, 1 :=
          Finset.sum_le_sum (fun k hk => nonsat_disch hrun (Finset.mem_range.mp hk))
      _ = K := by simp
  have hP := pass_core hrun
  have h2 : K ≤ Fintype.card V * passCount K S := by
    have := Finset.card_le_mul_card_image_of_maps_to (f := fun k => frontPass (S k))
      (s := Finset.range K) (t := Finset.Icc 1 (passCount K S))
      (fun k hk => by
        rw [Finset.mem_range] at hk; rw [Finset.mem_Icc]
        refine ⟨front_ge hrun hk, ?_⟩
        unfold passCount
        exact Finset.le_sup (f := fun k => frontPass (S k)) (Finset.mem_range.mpr hk))
      (Fintype.card V) (fun b _ => le_trans (Nat.le_add_right _ _) (tag_count hrun b K le_rfl))
    simpa using this
  calc nonsatPushCount N L K S J ≤ Fintype.card V * passCount K S := h1.trans h2
    _ ≤ Fintype.card V * (4 * Fintype.card V ^ 2) := Nat.mul_le_mul_left _ hP
    _ = 4 * Fintype.card V ^ 3 := by ring

end Run3
end GT
end GoldbergTarjan.FIFO

open GoldbergTarjan.FIFO


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    nonsatPushCount N L K S J ≤ 4 * Fintype.card V ^ 3 := by
  exact goal_core hrun
