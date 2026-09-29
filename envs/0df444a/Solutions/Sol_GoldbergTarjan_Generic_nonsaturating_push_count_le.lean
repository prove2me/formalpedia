-- Prove2me | solution 1 for GoldbergTarjan.Generic.nonsaturating_push_count_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:10:28.889957+00:00
-- url     : https://prove2.me/submissions/bc2625bb-dca1-4172-80bc-8e6da15a672f

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run



namespace GoldbergTarjan.Generic

open Classical

set_option linter.unusedSectionVars false
section MF
variable {V : Type} [Fintype V]

/-- unit flow on a pair -/
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

lemma path_flow (N : Network V) (f : V → V → ℝ) (a b : V) (hab : ResidualReachable N f a b) :
    ∃ h : V → V → ℝ, (∀ x y, h x y = - h y x) ∧ (∀ x y, 0 < h x y → IsResidualEdge N f x y) ∧
      ∀ u, excess h u = (if u = b then 1 else 0) - (if u = a then 1 else 0) := by
  induction hab with
  | refl => exact ⟨fun _ _ => 0, by simp, by simp, by intro u; simp [excess]⟩
  | tail _ hbc ih =>
    rename_i b c _
    obtain ⟨h, h1, h2, h3⟩ := ih
    refine ⟨fun x y => h x y + unitF b c x y, ?_, ?_, ?_⟩
    · intro x y; beta_reduce; rw [h1 x y, unitF_antisymm]; ring
    · intro x y hxy
      by_cases hp : x = b ∧ y = c
      · obtain ⟨rfl, rfl⟩ := hp; exact hbc
      · have : unitF b c x y ≤ 0 := by unfold unitF; rw [if_neg hp]; split_ifs <;> norm_num
        exact h2 x y (by linarith)
    · intro u; rw [excess_add, h3, excess_unitF]; ring

lemma sum_antisymm_zero (g : V → V → ℝ) (hg : ∀ x y, g x y = - g y x) (T : Finset V) :
    ∑ x ∈ T, ∑ y ∈ T, g x y = 0 := by
  have : ∑ x ∈ T, ∑ y ∈ T, g x y = - ∑ x ∈ T, ∑ y ∈ T, g x y := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]; congr 1; ext x; rw [← Finset.sum_neg_distrib]
    congr 1; ext y; rw [hg]
  linarith

/-- value of a flow equals the net flow across a cut containing s but not t -/
lemma value_eq_cut (N : Network V) (g : V → V → ℝ) (hg : IsFlow N g) (S : Finset V)
    (hs : N.s ∈ S) (ht : N.t ∉ S) :
    value N g = ∑ x ∈ S, ∑ u ∈ Sᶜ, g x u := by
  obtain ⟨_, ha, hc⟩ := hg
  have h1 : ∑ u ∈ Sᶜ, excess g u = value N g := by
    rw [Finset.sum_eq_single N.t]
    · rfl
    · intro u hu hut; apply hc u _ hut; intro h; subst h; simp at hu; exact hu hs
    · intro h; simp at h; exact absurd h ht
  rw [← h1]
  unfold excess
  have h2 : ∀ u, ∑ x, g x u = ∑ x ∈ S, g x u + ∑ x ∈ Sᶜ, g x u := by
    intro u; rw [Finset.sum_add_sum_compl]
  simp_rw [h2]
  rw [Finset.sum_add_distrib]
  have h3 : ∑ u ∈ Sᶜ, ∑ x ∈ Sᶜ, g x u = 0 := by
    rw [Finset.sum_comm]; exact sum_antisymm_zero g ha _
  rw [h3, add_zero, Finset.sum_comm]

theorem mf_core (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ResidualReachable N f N.s N.t := by
  constructor
  · rintro ⟨_, hmax⟩ hr
    obtain ⟨h, h1, h2, h3⟩ := path_flow N f _ _ hr
    -- choose ε
    have hev : ∀ᶠ ε in nhdsWithin (0:ℝ) (Set.Ioi 0), ∀ x y, f x y + ε * h x y ≤ N.c x y := by
      rw [Filter.eventually_all]; intro x; rw [Filter.eventually_all]; intro y
      by_cases hp : 0 < h x y
      · have hr' := h2 x y hp
        unfold IsResidualEdge residualCap at hr'
        have ht : Filter.Tendsto (fun ε : ℝ => f x y + ε * h x y) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x y + 0 * h x y)) := by
          apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
          exact ((continuous_id.mul continuous_const).const_add _).tendsto 0 |>.congr (fun _ => rfl)
        rw [zero_mul, add_zero] at ht
        exact ht.eventually (ge_mem_nhds (by linarith))
      · push_neg at hp
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have : ε * h x y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hε) hp
        linarith [hf.1 x y]
    obtain ⟨ε, hε1, hε2⟩ := (hev.and self_mem_nhdsWithin).exists
    have hflow : IsFlow N (fun x y => f x y + ε * h x y) := by
      refine ⟨hε1, ?_, ?_⟩
      · intro x y; beta_reduce; rw [hf.2.1 x y, h1 x y]; ring
      · intro u hus hut
        rw [excess_add, excess_smul (f := h), h3, hf.2.2 u hus hut]; simp [hus, hut]
    have hv := hmax _ hflow
    have : value N (fun x y => f x y + ε * h x y) = value N f + ε := by
      have e1 : value N (fun x y => f x y + ε * h x y) = excess (fun x y => f x y + ε * h x y) N.t := rfl
      rw [e1, excess_add, excess_smul (f := h), h3]
      simp [N.source_ne_sink.symm]; rfl
    rw [this] at hv
    have : (0:ℝ) < ε := hε2
    linarith
  · intro hnr
    refine ⟨hf, ?_⟩
    intro g hg
    set S : Finset V := Finset.univ.filter (fun u => ResidualReachable N f N.s u) with hS
    have hs : N.s ∈ S := by simp [hS]; exact Relation.ReflTransGen.refl
    have ht : N.t ∉ S := by simp [hS]; exact hnr
    rw [value_eq_cut N g hg S hs ht, value_eq_cut N f hf S hs ht]
    apply Finset.sum_le_sum; intro x hx; apply Finset.sum_le_sum; intro u hu
    have hfx : f x u = N.c x u := by
      by_contra hne
      have hlt : f x u < N.c x u := lt_of_le_of_ne (hf.1 x u) hne
      have : ResidualReachable N f N.s u := by
        simp [hS] at hx
        exact hx.tail (show IsResidualEdge N f x u by unfold IsResidualEdge residualCap; linarith)
      simp [hS] at hu; exact hu this
    rw [hfx]; exact hg.1 x u

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
    simp only [if_pos h1, if_neg h2]; ring
  · by_cases h2 : x = w ∧ y = v
    · simp only [if_neg h1, if_pos h2]; ring
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
    residualCap N (pushFlow N f v w) v w = residualCap N f v w - pushAmount N f v w := by
  unfold residualCap; rw [pushFlow_apply N f v w hvw, unitF_vw hvw]; ring

lemma res_push_le (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (a b v w : V)
    (hp : PushApplicable N f d a b) (hne : ¬ (a = w ∧ b = v)) :
    residualCap N (pushFlow N f a b) v w ≤ residualCap N f v w := by
  have hab := push_ne hp
  have hδ := (pushAmount_pos hp).le
  unfold residualCap; rw [pushFlow_apply N f a b hab]
  have : 0 ≤ unitF a b v w := unitF_nonneg_of (fun h => hne ⟨h.2.symm, h.1.symm⟩)
  nlinarith [mul_nonneg hδ this]

lemma push_preflow (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V) (hf : IsPreflow N f)
    (hp : PushApplicable N f d v w) : IsPreflow N (pushFlow N f v w) := by
  have hvw := push_ne hp
  have hδ0 := (pushAmount_pos hp).le
  have hδe : pushAmount N f v w ≤ excess f v := min_le_left _ _
  have hδr : pushAmount N f v w ≤ residualCap N f v w := min_le_right _ _
  refine ⟨?_, ?_, ?_⟩
  · intro x y; rw [pushFlow_apply N f v w hvw]
    by_cases h1 : x = v ∧ y = w
    · obtain ⟨rfl, rfl⟩ := h1; rw [unitF_vw hvw]; unfold residualCap at hδr; linarith
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

lemma push_valid (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞) (v w : V)
    (hd : IsValidLabeling N f d) (hp : PushApplicable N f d v w) :
    IsValidLabeling N (pushFlow N f v w) d := by
  have hvw := push_ne hp
  have hδ0 := (pushAmount_pos hp).le
  refine ⟨hd.1, hd.2.1, ?_⟩
  intro x y hxy
  by_cases h2 : x = w ∧ y = v
  · obtain ⟨rfl, rfl⟩ := h2; rw [hp.2.2]; exact le_self_add.trans le_self_add
  · apply hd.2.2
    unfold IsResidualEdge residualCap at hxy ⊢
    rw [pushFlow_apply N f v w hvw] at hxy
    have := unitF_nonneg_of (v := v) (w := w) h2
    nlinarith [mul_nonneg hδ0 this]

lemma relabel_ge {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v : V}
    (ha : RelabelApplicable N f d v) : d v + 1 ≤ relabelValue N f d v := by
  unfold relabelValue; apply le_iInf₂; intro w hw; exact add_le_add (ha.2 w hw) le_rfl

lemma relabel_le {N : Network V} {f : V → V → ℝ} {d : V → ℕ∞} {v w : V}
    (hw : 0 < residualCap N f v w) : relabelValue N f d v ≤ d w + 1 := iInf₂_le w hw

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
    have hxy : ¬ IsResidualEdge N f x y := by
      intro he
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl] at hx hy
      exact hy (hx.tail he)
    unfold IsResidualEdge residualCap at hxy; push_neg at hxy
    rw [hf.2.1 y x]; linarith [N.cap_nonneg x y]
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

/-- the invariant -/
def Inv (N : Network V) (p : State V) : Prop :=
  IsPreflow N p.1 ∧ IsValidLabeling N p.1 p.2 ∧
    ∀ v, p.2 v ≤ ((2 * Fintype.card V - 1 : ℕ) : ℕ∞)

lemma step_inv (N : Network V) (p q : State V) (hp : Inv N p) (hs : BasicStep N p q) :
    Inv N q ∧ ∀ v, p.2 v ≤ q.2 v := by
  rcases hs with ⟨v, w, hpush⟩ | ⟨v, hrel⟩
  · obtain ⟨happ, hq1, hq2⟩ := hpush
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hq1]; exact push_preflow N p.1 p.2 v w hp.1 happ
    · rw [hq1, hq2]; exact push_valid N p.1 p.2 v w hp.2.1 happ
    · rw [hq2]; exact hp.2.2
    · intro x; rw [hq2]
  · obtain ⟨happ, hq1, hq2⟩ := hrel
    have hmono : ∀ x, p.2 x ≤ q.2 x := by
      intro x; rw [hq2]; by_cases hx : x = v
      · subst hx; rw [Function.update_self]; exact le_self_add.trans (relabel_ge happ)
      · rw [Function.update_of_ne hx]
    have hvalid : IsValidLabeling N q.1 q.2 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [hq2, Function.update_of_ne happ.1.1.symm]; exact hp.2.1.1
      · rw [hq2, Function.update_of_ne happ.1.2.1.symm]; exact hp.2.1.2.1
      · intro x y hxy; rw [hq1] at hxy
        by_cases hx : x = v
        · subst hx
          have hl : q.2 x = relabelValue N p.1 p.2 x := by rw [hq2, Function.update_self]
          rw [hl]; exact (relabel_le hxy).trans (add_le_add (hmono y) le_rfl)
        · have hl : q.2 x = p.2 x := by rw [hq2, Function.update_of_ne hx]
          rw [hl]; exact (hp.2.1.2.2 x y hxy).trans (add_le_add (hmono y) le_rfl)
    refine ⟨⟨by rw [hq1]; exact hp.1, hvalid, ?_⟩, hmono⟩
    intro x
    by_cases hx : x = v
    · subst hx
      have hr := reach_source N p.1 hp.1 x happ.1.2.2.2
      rw [← hq1] at hr
      have := label_reach (IsResidualEdge N q.1) q.2 hvalid.2.2 hr (Fintype.card V) hvalid.1
      refine this.trans ?_
      exact_mod_cast (by omega : Fintype.card V + (Fintype.card V - 1) ≤ 2 * Fintype.card V - 1)
    · rw [hq2, Function.update_of_ne hx]; exact hp.2.2 x

lemma init_inv (N : Network V) : Inv N (initialState N) := by
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.s⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v w; simp only [initialState, initialFlow]; split_ifs with h1 h2
    · subst h1; exact le_rfl
    · have := N.cap_nonneg N.s v; have := N.cap_nonneg v w; linarith
    · exact N.cap_nonneg v w
  · intro v w; simp only [initialState, initialFlow]
    by_cases h1 : v = N.s <;> by_cases h2 : w = N.s <;> simp [h1, h2, N.cap_self]
  · intro v hv; unfold excess; simp only [initialState, initialFlow]
    rw [Finset.sum_eq_single N.s]
    · simp only [if_true]; exact N.cap_nonneg _ _
    · intro b _ hb; simp [hb, hv]
    · simp
  · simp [initialState, initialLabel]
  · simp [initialState, initialLabel, N.source_ne_sink.symm]
  · intro x y hxy; by_cases hx : x = N.s
    · exfalso; subst hx; unfold IsResidualEdge residualCap at hxy
      simp [initialState, initialFlow] at hxy
    · simp [initialState, initialLabel, hx]
  · intro x; simp only [initialState, initialLabel]; split_ifs
    · exact_mod_cast (by omega : Fintype.card V ≤ 2 * Fintype.card V - 1)
    · simp

section Run
variable {N : Network V} {σ : ℕ → State V} {K : ℕ}

lemma run_inv (hrun : IsRun N σ K) : ∀ k ≤ K, Inv N (σ k) := by
  intro k; induction k with
  | zero => intro _; rw [hrun.1]; exact init_inv N
  | succ k ih => intro hk; exact (step_inv N _ _ (ih (by omega)) (hrun.2 k (by omega))).1

lemma run_mono (hrun : IsRun N σ K) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ K) (v : V) :
    (σ j).2 v ≤ (σ k).2 v := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih =>
    exact (ih (by omega)).trans ((step_inv N _ _ (run_inv hrun k (by omega)) (hrun.2 k (by omega))).2 v)

end Run

noncomputable def lab (p : State V) (v : V) : ℕ := (p.2 v).toNat

lemma lab_cast {N : Network V} {p : State V} (hp : Inv N p) (v : V) : p.2 v = (lab p v : ℕ∞) := by
  unfold lab
  exact (ENat.natCast_toNat (lt_of_le_of_lt (hp.2.2 v) (ENat.natCast_lt_top _)).ne).symm

lemma lab_le {N : Network V} {p : State V} (hp : Inv N p) (v : V) :
    lab p v ≤ 2 * Fintype.card V - 1 := by
  have := hp.2.2 v; rw [lab_cast hp v] at this; exact_mod_cast this

lemma lab_eq {N : Network V} {p : State V} (hp : Inv N p) {x y : V} (h : p.2 x = p.2 y + 1) :
    lab p x = lab p y + 1 := by
  rw [lab_cast hp x, lab_cast hp y] at h; exact_mod_cast h

lemma lab_mono {N : Network V} {p q : State V} (hp : Inv N p) (hq : Inv N q) {x : V}
    (h : p.2 x ≤ q.2 x) : lab p x ≤ lab q x := by
  rw [lab_cast hp x, lab_cast hq x] at h; exact_mod_cast h


section Counts
variable {N : Network V} {σ : ℕ → State V} {K : ℕ}

lemma relabel_strict (hrun : IsRun N σ K) {k : ℕ} (hk : k < K) {v : V}
    (h : RelabelStep N (σ k) (σ (k + 1)) v) : lab (σ k) v < lab (σ (k + 1)) v := by
  have hp := run_inv hrun k hk.le
  have hq := run_inv hrun (k + 1) hk
  have h1 := relabel_ge h.1
  have h2 : (σ (k + 1)).2 v = relabelValue N (σ k).1 (σ k).2 v := by
    rw [h.2.2, Function.update_self]
  rw [← h2, lab_cast hp v, lab_cast hq v] at h1
  have : lab (σ k) v + 1 ≤ lab (σ (k + 1)) v := by exact_mod_cast h1
  omega

lemma lab_run_mono (hrun : IsRun N σ K) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ K) (v : V) :
    lab (σ j) v ≤ lab (σ k) v :=
  lab_mono (run_inv hrun j (hjk.trans hk)) (run_inv hrun k hk) (run_mono hrun j k hjk hk v)

lemma relabelAt_le (hrun : IsRun N σ K) (v : V) :
    relabelCountAt N σ K v ≤ 2 * Fintype.card V - 1 := by
  unfold relabelCountAt
  have hlt : ∀ k1 ∈ (Finset.range K).filter (fun k => RelabelStep N (σ k) (σ (k + 1)) v),
      ∀ k2 ∈ (Finset.range K).filter (fun k => RelabelStep N (σ k) (σ (k + 1)) v),
      k1 < k2 → lab (σ k1) v < lab (σ k2) v := by
    intro k1 hk1 k2 hk2 h12
    simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2
    exact lt_of_lt_of_le (relabel_strict hrun hk1.1 hk1.2) (lab_run_mono hrun (by omega) hk2.1.le v)
  have : ((Finset.range K).filter (fun k => RelabelStep N (σ k) (σ (k + 1)) v)).card ≤
      (Finset.range (2 * Fintype.card V - 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => lab (σ k) v)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Finset.mem_coe,
        Finset.mem_filter] at hk ⊢
      have := relabel_strict hrun hk.1 hk.2
      have := lab_le (run_inv hrun (k + 1) hk.1) v
      omega
    · intro k1 hk1 k2 hk2 heq
      simp only [Finset.mem_coe] at hk1 hk2
      rcases lt_trichotomy k1 k2 with h | h | h
      · exact absurd heq (hlt k1 hk1 k2 hk2 h).ne
      · exact h
      · exact absurd heq (hlt k2 hk2 k1 hk1 h).ne'
  simpa using this

lemma card_inner (N : Network V) :
    (Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t)).card = Fintype.card V - 2 := by
  have : Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t) = ({N.s, N.t} : Finset V)ᶜ := by
    ext x; simp
  rw [this, Finset.card_compl, Finset.card_pair N.source_ne_sink]

lemma card_two_le (N : Network V) : 2 ≤ Fintype.card V := by
  have := Finset.card_le_univ ({N.s, N.t} : Finset V)
  rw [Finset.card_pair N.source_ne_sink] at this; exact this

theorem relabel_core (hrun : IsRun N σ K) :
    (∀ v : V, relabelCountAt N σ K v ≤ 2 * Fintype.card V - 1) ∧
      relabelCount N σ K ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) ∧
      (2 * Fintype.card V - 1) * (Fintype.card V - 2) < 2 * Fintype.card V ^ 2 := by
  refine ⟨fun v => relabelAt_le hrun v, ?_, ?_⟩
  · have hsub : (Finset.range K).filter (fun k => ∃ v, RelabelStep N (σ k) (σ (k + 1)) v) ⊆
        (Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t)).biUnion
          (fun v => (Finset.range K).filter (fun k => RelabelStep N (σ k) (σ (k + 1)) v)) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      obtain ⟨hk, v, hv⟩ := hk
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_range]
      exact ⟨v, ⟨hv.1.1.1, hv.1.1.2.1⟩, hk, hv⟩
    unfold relabelCount
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t), relabelCountAt N σ K v :=
          Finset.card_biUnion_le
      _ ≤ ∑ v ∈ Finset.univ.filter (fun v : V => v ≠ N.s ∧ v ≠ N.t), (2 * Fintype.card V - 1) :=
          Finset.sum_le_sum (fun v _ => relabelAt_le hrun v)
      _ = (2 * Fintype.card V - 1) * (Fintype.card V - 2) := by
          rw [Finset.sum_const, card_inner N, smul_eq_mul, mul_comm]
  · have h2 := card_two_le N
    obtain ⟨a, ha⟩ : ∃ a, Fintype.card V = a + 2 := ⟨Fintype.card V - 2, by omega⟩
    rw [ha]
    have e1 : 2 * (a + 2) - 1 = 2 * a + 3 := by omega
    have e2 : a + 2 - 2 = a := by omega
    rw [e1, e2]; nlinarith

lemma sat_between (hrun : IsRun N σ K) {v w : V} {k1 k2 : ℕ} (h12 : k1 < k2) (hk2 : k2 < K)
    (h1s : residualCap N (σ (k1 + 1)).1 v w = 0) (h2 : PushStep N (σ k2) (σ (k2 + 1)) v w) :
    ∃ j, k1 < j ∧ j < k2 ∧ PushStep N (σ j) (σ (j + 1)) w v := by
  by_contra hno
  push_neg at hno
  have key : ∀ j, k1 + 1 ≤ j → j ≤ k2 → residualCap N (σ j).1 v w ≤ 0 := by
    intro j hj1 hj2
    induction j, hj1 using Nat.le_induction with
    | base => rw [h1s]
    | succ j hj ih =>
      have hr := ih (by omega)
      rcases hrun.2 j (by omega) with ⟨a, b, hab⟩ | ⟨a, hrel⟩
      · have hne : ¬ (a = w ∧ b = v) := by
          rintro ⟨rfl, rfl⟩; exact hno j (by omega) (by omega) hab
        rw [hab.2.1]
        exact (res_push_le N _ _ a b v w hab.1 hne).trans hr
      · rw [hrel.2.1]; exact hr
  have := key k2 (by omega) le_rfl
  have := h2.1.2.1
  linarith

lemma sat_gap (hrun : IsRun N σ K) {v w : V} {k1 k2 : ℕ} (h12 : k1 < k2) (hk2 : k2 < K)
    (h1 : PushStep N (σ k1) (σ (k1 + 1)) v w) (h1s : residualCap N (σ (k1 + 1)).1 v w = 0)
    (h2 : PushStep N (σ k2) (σ (k2 + 1)) v w) : lab (σ k1) v + 2 ≤ lab (σ k2) v := by
  obtain ⟨j, hj1, hj2, hj⟩ := sat_between hrun h12 hk2 h1s h2
  have e1 := lab_eq (run_inv hrun k1 (by omega)) h1.1.2.2
  have e2 := lab_eq (run_inv hrun j (by omega)) hj.1.2.2
  have e3 := lab_eq (run_inv hrun k2 (by omega)) h2.1.2.2
  have m1 := lab_run_mono hrun (j := k1) (k := j) (by omega) (by omega) v
  have m2 := lab_run_mono hrun (j := j) (k := k2) (by omega) (by omega) w
  omega

lemma satAt_le (hrun : IsRun N σ K) (v w : V) :
    ((Finset.range K).filter (fun k => PushStep N (σ k) (σ (k + 1)) v w ∧
      residualCap N (σ (k + 1)).1 v w = 0)).card ≤ Fintype.card V := by
  have hn := card_two_le N
  have hlt : ∀ k1 ∈ (Finset.range K).filter (fun k => PushStep N (σ k) (σ (k + 1)) v w ∧
        residualCap N (σ (k + 1)).1 v w = 0),
      ∀ k2 ∈ (Finset.range K).filter (fun k => PushStep N (σ k) (σ (k + 1)) v w ∧
        residualCap N (σ (k + 1)).1 v w = 0),
      k1 < k2 → (lab (σ k1) v - 1) / 2 < (lab (σ k2) v - 1) / 2 := by
    intro k1 hk1 k2 hk2 h12
    simp only [Finset.mem_filter, Finset.mem_range] at hk1 hk2
    have := sat_gap hrun h12 hk2.1 hk1.2.1 hk1.2.2 hk2.2.1
    have e1 := lab_eq (run_inv hrun k1 (by omega)) hk1.2.1.1.2.2
    omega
  have : ((Finset.range K).filter (fun k => PushStep N (σ k) (σ (k + 1)) v w ∧
      residualCap N (σ (k + 1)).1 v w = 0)).card ≤ (Finset.range (Fintype.card V)).card := by
    apply Finset.card_le_card_of_injOn (fun k => (lab (σ k) v - 1) / 2)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Finset.mem_coe,
        Finset.mem_filter] at hk ⊢
      have := lab_le (run_inv hrun k hk.1.le) v
      omega
    · intro k1 hk1 k2 hk2 heq
      simp only [Finset.mem_coe] at hk1 hk2
      rcases lt_trichotomy k1 k2 with h | h | h
      · exact absurd heq (hlt k1 hk1 k2 hk2 h).ne
      · exact h
      · exact absurd heq (hlt k2 hk2 k1 hk1 h).ne'
  simpa using this

theorem sat_core (hrun : IsRun N σ K) :
    saturatingPushCount N σ K ≤ 2 * Fintype.card V * N.numEdges := by
  set P : Finset (V × V) := Finset.univ.filter (fun p : V × V => 0 < N.c p.1 p.2 ∨ 0 < N.c p.2 p.1)
    with hP
  have hPc : P.card ≤ 2 * N.numEdges := by
    have hsub : P ⊆ N.edges ∪ N.edges.image Prod.swap := by
      intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_union, Network.edges, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image]
      rcases hp with h | h
      · exact Or.inl h
      · exact Or.inr ⟨(p.2, p.1), h, rfl⟩
    calc P.card ≤ _ := Finset.card_le_card hsub
      _ ≤ N.edges.card + (N.edges.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ N.edges.card + N.edges.card := add_le_add le_rfl Finset.card_image_le
      _ = 2 * N.numEdges := by unfold Network.numEdges; ring
  have hsub : (Finset.range K).filter (fun k => ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
      residualCap N (σ (k + 1)).1 v w = 0) ⊆
      P.biUnion (fun p => (Finset.range K).filter (fun k => PushStep N (σ k) (σ (k + 1)) p.1 p.2 ∧
        residualCap N (σ (k + 1)).1 p.1 p.2 = 0)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk, v, w, hv⟩ := hk
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    refine ⟨(v, w), ?_, hk, hv⟩
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
    have hinv := run_inv hrun k hk.le
    have hr := hv.1.1.2.1
    unfold residualCap at hr
    have ha := hinv.1.2.1 v w
    have hc := hinv.1.1 w v
    by_contra hcon; push_neg at hcon
    linarith [hcon.1, hcon.2]
  unfold saturatingPushCount
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, ((Finset.range K).filter (fun k => PushStep N (σ k) (σ (k + 1)) p.1 p.2 ∧
        residualCap N (σ (k + 1)).1 p.1 p.2 = 0)).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ P, Fintype.card V := Finset.sum_le_sum (fun p _ => satAt_le hrun p.1 p.2)
    _ = P.card * Fintype.card V := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * N.numEdges * Fintype.card V := Nat.mul_le_mul_right _ hPc
    _ = 2 * Fintype.card V * N.numEdges := by ring

noncomputable def Phi (N : Network V) (p : State V) : ℕ :=
  ∑ v, if IsActive N p.1 p.2 v then lab p v else 0

noncomputable def Lsum (p : State V) : ℕ := ∑ v, lab p v

lemma phi_push {p q : State V} {v w : V} (h : PushStep N p q v w) :
    Phi N q + (if 0 < residualCap N q.1 v w then lab p v else 0) ≤ Phi N p + lab p w := by
  obtain ⟨happ, hq1, hq2⟩ := h
  have hvw := push_ne happ
  have hlabq : ∀ x, lab q x = lab p x := by intro x; unfold lab; rw [hq2]
  have hact_other : ∀ x, x ≠ v → x ≠ w → (IsActive N q.1 q.2 x ↔ IsActive N p.1 p.2 x) := by
    intro x hxv hxw; unfold IsActive; rw [hq1, hq2, excess_push_other N p.1 v w x hvw hxv hxw]
  have hle : ∀ x, (if IsActive N q.1 q.2 x then lab q x else 0) ≤ lab p x := by
    intro x; rw [hlabq]; split_ifs <;> omega
  have hsum : ∀ x, (if IsActive N q.1 q.2 x then lab q x else 0) +
      (if x = v then (if 0 < residualCap N q.1 v w then lab p v else 0) else 0)
       ≤ (if IsActive N p.1 p.2 x then lab p x else 0) + (if x = w then lab p w else 0) := by
    intro x
    by_cases hxv : x = v
    · subst hxv
      rw [if_pos rfl, if_neg hvw, if_pos happ.1]
      by_cases hr : 0 < residualCap N q.1 x w
      · have hna : ¬ IsActive N q.1 q.2 x := by
          intro hact
          have hδ : pushAmount N p.1 x w = excess p.1 x := by
            rw [hq1, res_push_vw N p.1 x w hvw] at hr
            rcases min_choice (excess p.1 x) (residualCap N p.1 x w) with h | h
            · exact h
            · exfalso; unfold pushAmount at hr; rw [h] at hr; linarith
          have := hact.2.2.2
          rw [hq1, excess_push_v N p.1 x w hvw, hδ] at this; linarith
        rw [if_neg hna, if_pos hr]; omega
      · rw [if_neg hr]; have := hle x; omega
    · by_cases hxw : x = w
      · subst hxw; rw [if_neg hxv, if_pos rfl]; have := hle x; omega
      · rw [if_neg hxv, if_neg hxw, hlabq]
        by_cases ha : IsActive N p.1 p.2 x
        · rw [if_pos ha, if_pos ((hact_other x hxv hxw).mpr ha)]
        · rw [if_neg ha, if_neg (fun h => ha ((hact_other x hxv hxw).mp h))]
  have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hsum x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq'] at this
  simpa [Phi] using this

lemma phi_relabel {p q : State V} (hp : Inv N p) (hq : Inv N q) {v : V}
    (h : RelabelStep N p q v) : Phi N q + Lsum p ≤ Phi N p + Lsum q := by
  have hmono : ∀ x, lab p x ≤ lab q x :=
    fun x => lab_mono hp hq ((step_inv N p q hp (Or.inr ⟨v, h⟩)).2 x)
  have hact : ∀ x, IsActive N q.1 q.2 x ↔ IsActive N p.1 p.2 x := by
    intro x; unfold IsActive; rw [h.2.1, lab_cast hq x, lab_cast hp x]
    simp [ENat.natCast_lt_top]
  have hsum : ∀ x, (if IsActive N q.1 q.2 x then lab q x else 0) + lab p x ≤
      (if IsActive N p.1 p.2 x then lab p x else 0) + lab q x := by
    intro x
    have := hmono x
    by_cases ha : IsActive N p.1 p.2 x
    · rw [if_pos ha, if_pos ((hact x).mpr ha)]; omega
    · rw [if_neg ha, if_neg (fun h => ha ((hact x).mp h))]; omega
  have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hsum x)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at this
  simpa [Phi, Lsum] using this

lemma lsum_push {p q : State V} {v w : V} (h : PushStep N p q v w) : Lsum q = Lsum p := by
  unfold Lsum lab; rw [h.2.2]

lemma nonsat_step (hrun : IsRun N σ K) {k : ℕ} (hk : k < K) :
    Phi N (σ (k + 1)) + Lsum (σ k) + (if (∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
      0 < residualCap N (σ (k + 1)).1 v w) then 1 else 0)
    ≤ Phi N (σ k) + Lsum (σ (k + 1)) + (2 * Fintype.card V - 1) *
      (if (∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
        residualCap N (σ (k + 1)).1 v w = 0) then 1 else 0) := by
  have hp := run_inv hrun k hk.le
  have hq := run_inv hrun (k + 1) hk
  have hX : 0 ≤ (2 * Fintype.card V - 1) * (if (∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
        residualCap N (σ (k + 1)).1 v w = 0) then 1 else 0) := Nat.zero_le _
  by_cases hns : ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧ 0 < residualCap N (σ (k + 1)).1 v w
  · rw [if_pos hns]
    obtain ⟨v, w, hpush, hr⟩ := hns
    have h1 := phi_push hpush
    rw [if_pos hr] at h1
    have h2 := lsum_push hpush
    have h3 := lab_eq hp hpush.1.2.2
    omega
  · rw [if_neg hns]
    by_cases hs : ∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧ residualCap N (σ (k + 1)).1 v w = 0
    · rw [if_pos hs, mul_one]
      obtain ⟨v, w, hpush, hr⟩ := hs
      have h1 := phi_push hpush
      rw [if_neg (by rw [hr]; exact lt_irrefl 0)] at h1
      have h2 := lsum_push hpush
      have h4 := lab_le hp w
      omega
    · rw [if_neg hs, mul_zero]
      rcases hrun.2 k hk with ⟨v, w, hpush⟩ | ⟨v, hrel⟩
      · exfalso
        have hvw := push_ne hpush.1
        have hge : 0 ≤ residualCap N (σ (k + 1)).1 v w := by
          rw [hpush.2.1, res_push_vw N _ v w hvw]
          have : pushAmount N (σ k).1 v w ≤ residualCap N (σ k).1 v w := min_le_right _ _
          linarith
        rcases hge.lt_or_eq with h | h
        · exact hns ⟨v, w, hpush, h⟩
        · exact hs ⟨v, w, hpush, h.symm⟩
      · have := phi_relabel hp hq hrel
        omega

lemma nonsat_sum (hrun : IsRun N σ K) : ∀ k ≤ K,
    Phi N (σ k) + Lsum (σ 0) + nonsaturatingPushCount N σ k ≤
      Phi N (σ 0) + Lsum (σ k) + (2 * Fintype.card V - 1) * saturatingPushCount N σ k := by
  intro k
  induction k with
  | zero => intro _; simp [nonsaturatingPushCount, saturatingPushCount]
  | succ k ih =>
    intro hk
    have c1 : nonsaturatingPushCount N σ (k + 1) = nonsaturatingPushCount N σ k +
        (if (∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
          0 < residualCap N (σ (k + 1)).1 v w) then 1 else 0) := by
      unfold nonsaturatingPushCount; rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    have c2 : saturatingPushCount N σ (k + 1) = saturatingPushCount N σ k +
        (if (∃ v w, PushStep N (σ k) (σ (k + 1)) v w ∧
          residualCap N (σ (k + 1)).1 v w = 0) then 1 else 0) := by
      unfold saturatingPushCount; rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    have h1 := ih (by omega)
    have h2 := nonsat_step hrun (k := k) (by omega)
    rw [c1, c2, mul_add]
    linarith

theorem nonsat_core (hm : Fintype.card V - 1 ≤ N.numEdges) (hrun : IsRun N σ K) :
    nonsaturatingPushCount N σ K ≤ 4 * Fintype.card V ^ 2 * N.numEdges := by
  have h1 := nonsat_sum hrun K le_rfl
  have hphi0 : Phi N (σ 0) = 0 := by
    unfold Phi; apply Finset.sum_eq_zero; intro x _
    split_ifs with ha
    · unfold lab; rw [hrun.1]; simp [initialState, initialLabel, ha.1]
    · rfl
  have hp0 := run_inv hrun 0 (Nat.zero_le _)
  have hpK := run_inv hrun K le_rfl
  have hL : Lsum (σ K) ≤ Lsum (σ 0) + (Fintype.card V - 2) * (2 * Fintype.card V - 1) := by
    have hpt : ∀ x, lab (σ K) x ≤ lab (σ 0) x +
        (if (x ≠ N.s ∧ x ≠ N.t) then 2 * Fintype.card V - 1 else 0) := by
      intro x
      by_cases hs : x = N.s
      · have a1 := hpK.2.1.1; have a2 := hp0.2.1.1
        rw [← hs] at a1 a2
        rw [lab_cast hpK] at a1; rw [lab_cast hp0] at a2
        have b1 : lab (σ K) x = Fintype.card V := by exact_mod_cast a1
        have b2 : lab (σ 0) x = Fintype.card V := by exact_mod_cast a2
        omega
      · by_cases ht : x = N.t
        · have a1 := hpK.2.1.2.1
          rw [← ht] at a1
          rw [lab_cast hpK] at a1
          have b1 : lab (σ K) x = 0 := by exact_mod_cast a1
          omega
        · rw [if_pos ⟨hs, ht⟩]; have := lab_le hpK x; omega
    have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpt x)
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, card_inner N,
      smul_eq_mul] at this
    exact this
  have hsat := sat_core hrun
  have h2 : (2 * Fintype.card V - 1) * saturatingPushCount N σ K ≤
      (2 * Fintype.card V - 1) * (2 * Fintype.card V * N.numEdges) := Nat.mul_le_mul_left _ hsat
  have hn := card_two_le N
  obtain ⟨a, ha⟩ : ∃ a, Fintype.card V = a + 2 := ⟨Fintype.card V - 2, by omega⟩
  rw [ha] at h2 hL hm h1 ⊢
  have e1 : 2 * (a + 2) - 1 = 2 * a + 3 := by omega
  have e2 : a + 2 - 2 = a := by omega
  have e3 : a + 2 - 1 = a + 1 := by omega
  rw [e1] at h2 hL h1; rw [e2] at hL; rw [e3] at hm
  rw [hphi0] at h1
  nlinarith

end Counts

end GT
end GoldbergTarjan.Generic

open GoldbergTarjan.Generic


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hm : Fintype.card V - 1 ≤ N.numEdges)
    (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    nonsaturatingPushCount N σ K ≤ 4 * Fintype.card V ^ 2 * N.numEdges := by
  exact nonsat_core hm hrun
