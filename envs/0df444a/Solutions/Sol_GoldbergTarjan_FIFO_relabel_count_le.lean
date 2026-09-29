-- Prove2me | solution 1 for GoldbergTarjan.FIFO.relabel_count_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:24:26.31814+00:00
-- url     : https://prove2.me/submissions/445cbc24-6b6c-49e8-a0a2-e39454a7833b

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts



namespace GoldbergTarjan.FIFO

open Classical

set_option linter.unusedSectionVars false
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
end GT
end GoldbergTarjan.FIFO

open GoldbergTarjan.FIFO


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    (∀ x, relabelCountAt N L K S J x ≤ 2 * Fintype.card V - 1) ∧
    relabelCount N L K S J ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
    (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by
  exact relabel_count_core hrun
