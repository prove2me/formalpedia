-- Prove2me | solution 1 for MetricTSP.pm_polytope_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-25T06:23:28.903731+00:00
-- url     : https://prove2.me/submissions/9fcd69c2-68fb-4840-bcb6-accf2cfe1fd1

import Mathlib
import Definitions.Def_MetricTSP_model
import Theorems.Thm_MetricTSP_support_perturbation

set_option maxHeartbeats 2000000

namespace MetricTSP

variable {n : ℕ}

/-! ### Setup

We prove Edmonds' perfect matching polytope theorem in convex-decomposition
form by strong induction on `(|W|, |supp y|)`.  `Feas` collects the polytope
membership conditions, `IsDecomp` the required decomposition. -/

def Feas (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ) : Prop :=
  (∀ u v, y u v = y v u) ∧ (∀ u v, 0 ≤ y u v) ∧ (∀ v, y v v = 0) ∧
    (∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W) ∧ (∀ v ∈ W, ∑ u, y v u = 1) ∧
    (∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v)

def IsDecomp (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ)
    (L : List (ℝ × (Fin n → Fin n))) : Prop :=
  L ≠ [] ∧
    (∀ p ∈ L, 0 < p.1 ∧
      (∀ v ∈ W, p.2 v ∈ W ∧ p.2 (p.2 v) = v ∧ p.2 v ≠ v) ∧
      (∀ v ∉ W, p.2 v = v)) ∧
    (L.map Prod.fst).sum = 1 ∧
    (∀ u v, y u v
      = (L.map (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0)).sum)

/-! ### List utilities -/

lemma list_sum_nonneg {α : Type} (L : List α) (f : α → ℝ)
    (h : ∀ a ∈ L, 0 ≤ f a) : 0 ≤ (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    linarith

lemma list_sum_single_le {α : Type} (L : List α) (f : α → ℝ) (a : α)
    (ha : a ∈ L) (h : ∀ b ∈ L, 0 ≤ f b) : f a ≤ (L.map f).sum := by
  induction L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with h1 | h1
    · subst h1
      have h2 := list_sum_nonneg l f (fun b hb => h b (List.mem_cons_of_mem a hb))
      linarith
    · have h2 := ih h1 (fun b hb => h b (List.mem_cons_of_mem c hb))
      have h3 := h c List.mem_cons_self
      linarith

lemma list_sum_scale {α : Type} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map (fun a => c * f a)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

lemma list_sum_congr {α : Type} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, f a = g a) : (L.map f).sum = (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

lemma list_sum_pos_of_mem {α : Type} (L : List α) (f : α → ℝ) (a : α)
    (ha : a ∈ L) (hpos : 0 < f a) (h : ∀ b ∈ L, 0 ≤ f b) :
    0 < (L.map f).sum :=
  lt_of_lt_of_le hpos (list_sum_single_le L f a ha h)

lemma list_map_zero_sum {α : Type} : ∀ L : List α,
    (L.map (fun _ => (0 : ℝ))).sum = 0
  | [] => by simp
  | a :: l => by simp [list_map_zero_sum l]

lemma list_sum_zero_of_all {α : Type} (L : List α) (f : α → ℝ)
    (h : ∀ a ∈ L, f a = 0) : (L.map f).sum = 0 := by
  rw [list_sum_congr L f (fun _ => 0) h]
  exact list_map_zero_sum L

/-- Exchange a `Finset` sum with a list sum. -/
lemma list_finset_swap {α : Type} {β : Type} (L : List α) (s : Finset β)
    (F : α → β → ℝ) :
    ∑ b ∈ s, (L.map (fun a => F a b)).sum
      = (L.map (fun a => ∑ b ∈ s, F a b)).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, ih]

lemma list_sum_scale_right {α : Type} (L : List α) (f : α → ℝ) (c : ℝ) :
    (L.map (fun a => f a * c)).sum = (L.map f).sum * c := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

lemma list_flatMap_sum {γ δ : Type} (L : List γ) (f : γ → List δ) (g : δ → ℝ) :
    ((L.flatMap f).map g).sum = (L.map (fun a => ((f a).map g).sum)).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons]

lemma list_sum_add {γ : Type} (L : List γ) (f g : γ → ℝ) :
    (L.map (fun a => f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    ring

lemma list_double_swap {γ δ : Type} (L₁ : List γ) (L₂ : List δ) (f : γ → δ → ℝ) :
    (L₁.map (fun p => (L₂.map (fun q => f p q)).sum)).sum
      = (L₂.map (fun q => (L₁.map (fun p => f p q)).sum)).sum := by
  induction L₁ with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact (list_sum_zero_of_all L₂ _ (fun q _ => rfl)).symm
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, ← list_sum_add]

lemma list_filter_sum {γ : Type} (L : List (ℝ × γ)) (g : (ℝ × γ) → ℝ)
    (hg : ∀ r ∈ L, ¬(0 < r.1) → g r = 0) :
    (((L.filter (fun r => decide (0 < r.1))).map g)).sum = (L.map g).sum := by
  classical
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases h : 0 < a.1
    · rw [if_pos (by simpa using h)]
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun r hr => hg r (List.mem_cons_of_mem a hr))]
    · rw [if_neg (by simpa using h)]
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun r hr => hg r (List.mem_cons_of_mem a hr)),
        hg a List.mem_cons_self h]
      ring

lemma list_group {γ : Type} (L : List (ℝ × γ)) (key : γ → Fin n) (G : Fin n → ℝ) :
    (L.map (fun p => p.1 * G (key p.2))).sum
      = ∑ b, (L.map (fun p => if key p.2 = b then p.1 else 0)).sum * G b := by
  classical
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
    (list_sum_scale_right L (fun p => if key p.2 = b then p.1 else 0) (G b)).symm),
    list_finset_swap]
  refine list_sum_congr _ _ _ (fun p _ => ?_)
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => by
    rw [show (if key p.2 = b then p.1 else 0) * G b
      = if key p.2 = b then p.1 * G b else 0 from by
        by_cases h : key p.2 = b
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]; ring]),
    Finset.sum_ite_eq Finset.univ (key p.2) (fun b => p.1 * G b),
    if_pos (Finset.mem_univ _)]

lemma cut_swap (y' : Fin n → Fin n → ℝ) (hsym' : ∀ u v, y' u v = y' v u)
    (A B : Finset (Fin n)) :
    ∑ u ∈ A, ∑ v ∈ B, y' u v = ∑ u ∈ B, ∑ v ∈ A, y' u v := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun u _ =>
    Finset.sum_congr rfl (fun v _ => hsym' v u))

/-! ### The empty case -/

lemma decomp_empty (y : Fin n → Fin n → ℝ)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ (∅ : Finset (Fin n)) ∧ v ∈ (∅ : Finset (Fin n))) :
    IsDecomp ∅ y [((1 : ℝ), id)] := by
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨by norm_num, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v _ => rfl⟩
  · intro u v
    have hy : y u v = 0 := by
      by_contra h0
      exact Finset.notMem_empty u (hsupp u v h0).1
    rw [hy]
    simp

/-! ### Handler 1: stripping a unit entry -/

lemma decomp_strip (N : ℕ)
    (oracle : ∀ (W' : Finset (Fin n)) (y' : Fin n → Fin n → ℝ),
      W'.card ≤ N → Even W'.card → Feas W' y' →
      ∃ L, IsDecomp W' y' L)
    (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ)
    (hcard : W.card ≤ N + 2) (hW : Even W.card) (hfeas : Feas W y)
    (a b : Fin n) (hab : y a b = 1) :
    ∃ L, IsDecomp W y L := by
  classical
  obtain ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ := hfeas
  have haW : a ∈ W := (hsupp a b (by rw [hab]; norm_num)).1
  have hbW : b ∈ W := (hsupp a b (by rw [hab]; norm_num)).2
  have hne : a ≠ b := by
    intro h
    rw [h, hdiag b] at hab
    norm_num at hab
  -- the two unit rows carry no other mass
  have hrow : ∀ v w : Fin n, v ∈ W → y v w = 1 → ∀ u, u ≠ w → y v u = 0 := by
    intro v w hv hvw u hu
    have hd := hdeg v hv
    have hsum : ∑ x ∈ (Finset.univ.erase w), y v x = 0 := by
      have h1 : ∑ x ∈ Finset.univ.erase w, y v x + y v w = ∑ x, y v x :=
        Finset.sum_erase_add _ _ (Finset.mem_univ w)
      rw [hd, hvw] at h1
      linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => hnn v x)).mp hsum u (Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩)
    exact this
  have hrowa : ∀ u, u ≠ b → y a u = 0 := hrow a b haW hab
  have hrowb : ∀ u, u ≠ a → y b u = 0 :=
    hrow b a hbW (by rw [← hsym a b]; exact hab)
  -- the reduced instance
  set W' := W \ {a, b} with hW'def
  obtain ⟨y', hy'⟩ : ∃ y' : Fin n → Fin n → ℝ, ∀ u v, y' u v
      = if u = a ∨ u = b ∨ v = a ∨ v = b then 0 else y u v :=
    ⟨_, fun _ _ => rfl⟩
  have habW : ({a, b} : Finset (Fin n)) ⊆ W := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact haW
    · rw [Finset.mem_singleton.mp h]; exact hbW
  have hcard' : W'.card = W.card - 2 := by
    rw [hW'def, Finset.card_sdiff, Finset.inter_eq_left.mpr habW,
      Finset.card_insert_of_notMem
        (fun h => hne (Finset.mem_singleton.mp h)), Finset.card_singleton]
  have hmemW' : ∀ x, x ∈ W' ↔ x ∈ W ∧ x ≠ a ∧ x ≠ b := by
    intro x
    rw [hW'def, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hfeas' : Feas W' y' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u v
      rw [hy' u v, hy' v u]
      by_cases h : u = a ∨ u = b ∨ v = a ∨ v = b
      · rw [if_pos h, if_pos (by tauto)]
      · rw [if_neg h, if_neg (by tauto), hsym]
    · intro u v
      rw [hy' u v]
      by_cases h : u = a ∨ u = b ∨ v = a ∨ v = b
      · rw [if_pos h]
      · rw [if_neg h]
        exact hnn u v
    · intro v
      rw [hy' v v]
      by_cases h : v = a ∨ v = b ∨ v = a ∨ v = b
      · rw [if_pos h]
      · rw [if_neg h]
        exact hdiag v
    · intro u v h0
      rw [hy' u v] at h0
      by_cases h : u = a ∨ u = b ∨ v = a ∨ v = b
      · rw [if_pos h] at h0
        norm_num at h0
      · rw [if_neg h] at h0
        push_neg at h
        obtain ⟨h1, h2⟩ := hsupp u v h0
        exact ⟨(hmemW' u).mpr ⟨h1, h.1, h.2.1⟩,
          (hmemW' v).mpr ⟨h2, h.2.2.1, h.2.2.2⟩⟩
    · intro v hv
      obtain ⟨hvW, hva, hvb⟩ := (hmemW' v).mp hv
      have hpt : ∀ u : Fin n, y' v u
          = y v u - ((if u = a then y v a else 0) + (if u = b then y v b else 0)) := by
        intro u
        rw [hy' v u]
        by_cases hua : u = a
        · rw [if_pos (by tauto), if_pos hua,
            if_neg (fun h => hne (hua.symm.trans h))]
          rw [hua]
          ring
        · by_cases hub : u = b
          · rw [if_pos (by tauto), if_neg hua, if_pos hub, hub]
            ring
          · rw [if_neg (by tauto), if_neg hua, if_neg hub]
            ring
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hpt u),
        Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ a (fun _ => y v a),
        Finset.sum_ite_eq' Finset.univ b (fun _ => y v b),
        if_pos (Finset.mem_univ a), if_pos (Finset.mem_univ b),
        hdeg v hvW, hsym v a, hrowa v hvb, hsym v b, hrowb v hva]
      ring
    · intro S hSW' hSodd
      have hSW : S ⊆ W := fun {x} hx => ((hmemW' x).mp (hSW' hx)).1
      have hcut := hodd S hSW hSodd
      have hpt : ∀ u ∈ S, ∀ v ∈ W' \ S, y' u v = y u v := by
        intro u hu v hv
        obtain ⟨hu1, hu2, hu3⟩ := (hmemW' u).mp (hSW' hu)
        obtain ⟨hv1, hv2, hv3⟩ := (hmemW' v).mp (Finset.mem_sdiff.mp hv).1
        rw [hy' u v, if_neg (by tauto)]
      have hsub : ∀ u ∈ S, ∑ v ∈ W' \ S, y u v = ∑ v ∈ W \ S, y u v := by
        intro u hu
        obtain ⟨hu1, hu2, hu3⟩ := (hmemW' u).mp (hSW' hu)
        refine Finset.sum_subset ?_ ?_
        · intro x hx
          obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
          exact Finset.mem_sdiff.mpr ⟨((hmemW' x).mp hx1).1, hx2⟩
        · intro x hx hx'
          obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
          have hxab : x = a ∨ x = b := by
            by_contra hc
            push_neg at hc
            exact hx' (Finset.mem_sdiff.mpr ⟨(hmemW' x).mpr ⟨hx1, hc.1, hc.2⟩, hx2⟩)
          rcases hxab with h | h
          · rw [h, hsym u a]
            exact hrowa u hu3
          · rw [h, hsym u b]
            exact hrowb u hu2
      calc (1 : ℝ) ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v := hcut
        _ = ∑ u ∈ S, ∑ v ∈ W' \ S, y u v :=
            (Finset.sum_congr rfl (fun u hu => hsub u hu)).symm
        _ = ∑ u ∈ S, ∑ v ∈ W' \ S, y' u v :=
            Finset.sum_congr rfl (fun u hu =>
              Finset.sum_congr rfl (fun v hv => (hpt u hu v hv).symm))
  -- recurse and re-attach the pair
  obtain ⟨L', hL'ne, hL'mem, hL'sum, hL'dec⟩ := oracle W' y'
    (by omega) (by
      obtain ⟨r, hr⟩ := hW
      have h2 : 2 ≤ W.card := by
        have := Finset.card_le_card habW
        rw [Finset.card_insert_of_notMem
          (fun h => hne (Finset.mem_singleton.mp h)), Finset.card_singleton] at this
        omega
      exact ⟨r - 1, by omega⟩) hfeas'
  set extf : (Fin n → Fin n) → (Fin n → Fin n) :=
    fun f => fun x => if x = a then b else if x = b then a else f x with hextdef
  have hextval : ∀ (f : Fin n → Fin n) (x : Fin n),
      extf f x = if x = a then b else if x = b then a else f x := fun _ _ => rfl
  refine ⟨L'.map (fun p => (p.1, extf p.2)), ?_, ?_, ?_, ?_⟩
  · intro h
    rw [List.map_eq_nil_iff] at h
    exact hL'ne h
  · intro p hp
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    obtain ⟨hpos, hpair, hfix⟩ := hL'mem p' hp'
    refine ⟨hpos, ?_, ?_⟩
    · intro v hv
      show extf p'.2 v ∈ W ∧ extf p'.2 (extf p'.2 v) = v ∧ extf p'.2 v ≠ v
      by_cases hva : v = a
      · have h1 : extf p'.2 v = b := by
          rw [hextval, if_pos hva]
        have h2 : extf p'.2 b = a := by
          rw [hextval, if_neg (fun h : b = a => hne h.symm), if_pos rfl]
        rw [h1, h2, hva]
        exact ⟨hbW, rfl, fun h => hne h.symm⟩
      · by_cases hvb : v = b
        · have h1 : extf p'.2 v = a := by
            rw [hextval, if_neg hva, if_pos hvb]
          have h2 : extf p'.2 a = b := by
            rw [hextval, if_pos rfl]
          rw [h1, h2, hvb]
          exact ⟨haW, rfl, hne⟩
        · have hvW' : v ∈ W' := (hmemW' v).mpr ⟨hv, hva, hvb⟩
          obtain ⟨h1, h2, h3⟩ := hpair v hvW'
          obtain ⟨h1W, h1a, h1b⟩ := (hmemW' _).mp h1
          have he1 : extf p'.2 v = p'.2 v := by
            rw [hextval, if_neg hva, if_neg hvb]
          have he2 : extf p'.2 (p'.2 v) = p'.2 (p'.2 v) := by
            rw [hextval, if_neg h1a, if_neg h1b]
          rw [he1, he2, h2]
          exact ⟨h1W, rfl, h3⟩
    · intro v hv
      show extf p'.2 v = v
      have hva : v ≠ a := fun h => hv (h ▸ haW)
      have hvb : v ≠ b := fun h => hv (h ▸ hbW)
      rw [hextval, if_neg hva, if_neg hvb]
      exact hfix v (fun h => hv ((hmemW' v).mp h).1)
  · rw [List.map_map]
    exact hL'sum
  · intro u v
    rw [List.map_map]
    have hcomp : ∀ p' : ℝ × (Fin n → Fin n),
        ((fun p : ℝ × (Fin n → Fin n) =>
          if p.2 u = v ∧ u ∈ W then p.1 else 0) ∘
          (fun p => (p.1, extf p.2))) p'
        = if extf p'.2 u = v ∧ u ∈ W then p'.1 else 0 := fun _ => rfl
    rw [List.map_congr_left (fun p' _ => hcomp p')]
    by_cases hua : u = a
    · subst hua
      have hext : ∀ f : Fin n → Fin n, extf f u = b := by
        intro f
        rw [hextval, if_pos rfl]
      rw [list_sum_congr _ _
        (fun p' => if b = v ∧ u ∈ W then p'.1 else 0)
        (fun p' _ => by rw [hext p'.2])]
      by_cases hvb : b = v
      · have h1 : y u v = 1 := by rw [← hvb]; exact hab
        rw [h1, list_sum_congr _ _ Prod.fst
          (fun p' _ => if_pos ⟨hvb, haW⟩), hL'sum]
      · have h1 : y u v = 0 := hrowa v (fun h => hvb h.symm)
        rw [h1, list_sum_zero_of_all _ _
          (fun p' _ => if_neg (fun hh => hvb hh.1))]
    · by_cases hub : u = b
      · subst hub
        have hext : ∀ f : Fin n → Fin n, extf f u = a := by
          intro f
          rw [hextval, if_neg (fun h : u = a => hne h.symm), if_pos rfl]
        rw [list_sum_congr _ _
          (fun p' => if a = v ∧ u ∈ W then p'.1 else 0)
          (fun p' _ => by rw [hext p'.2])]
        by_cases hva : a = v
        · have h1 : y u v = 1 := by rw [← hva, ← hsym a u]; exact hab
          rw [h1, list_sum_congr _ _ Prod.fst
            (fun p' _ => if_pos ⟨hva, hbW⟩), hL'sum]
        · have h1 : y u v = 0 := hrowb v (fun h => hva h.symm)
          rw [h1, list_sum_zero_of_all _ _
            (fun p' _ => if_neg (fun hh => hva hh.1))]
      · have hext : ∀ f : Fin n → Fin n, extf f u = f u := by
          intro f
          rw [hextval, if_neg hua, if_neg hub]
        rw [list_sum_congr _ _
          (fun p' => if p'.2 u = v ∧ u ∈ W then p'.1 else 0)
          (fun p' _ => by rw [hext p'.2])]
        by_cases huW : u ∈ W
        · have huW' : u ∈ W' := (hmemW' u).mpr ⟨huW, hua, hub⟩
          by_cases hva : v = a
          · have h1 : y u v = 0 := by
              rw [hva, hsym u a]
              exact hrowa u (fun h => hub h)
            rw [h1, list_sum_zero_of_all _ _ (fun p' hp' => ?_)]
            refine if_neg (fun hh => ?_)
            have hmem := ((hL'mem p' hp').2.1 u huW').1
            rw [hh.1, hva] at hmem
            exact ((hmemW' a).mp hmem).2.1 rfl
          · by_cases hvb : v = b
            · have h1 : y u v = 0 := by
                rw [hvb, hsym u b]
                exact hrowb u (fun h => hua h)
              rw [h1, list_sum_zero_of_all _ _ (fun p' hp' => ?_)]
              refine if_neg (fun hh => ?_)
              have hmem := ((hL'mem p' hp').2.1 u huW').1
              rw [hh.1, hvb] at hmem
              exact ((hmemW' b).mp hmem).2.2 rfl
            · have h1 : y u v = y' u v := by
                rw [hy' u v, if_neg (by tauto)]
              rw [h1, hL'dec u v]
              exact list_sum_congr _ _ _ (fun p' _ => by
                by_cases hp2 : p'.2 u = v
                · rw [if_pos ⟨hp2, huW'⟩, if_pos ⟨hp2, huW⟩]
                · rw [if_neg (fun hh => hp2 hh.1), if_neg (fun hh => hp2 hh.1)])
        · have h1 : y u v = 0 := by
            by_contra h0
            exact huW (hsupp u v h0).1
          rw [h1, list_sum_zero_of_all _ _
            (fun p' _ => if_neg (fun hh => huW hh.2))]


/-! ### Contraction of one side of a tight cut -/

lemma contract_feas (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ)
    (hfeas : Feas W y)
    (A B : Finset (Fin n)) (hpart : W = A ∪ B) (hdisj : Disjoint A B)
    (hAodd : Odd A.card) (rep : Fin n) (hrep : rep ∈ B)
    (htight : ∑ u ∈ A, ∑ v ∈ B, y u v = 1) :
    ∃ yc : Fin n → Fin n → ℝ,
      (∀ u v, yc u v = if u ∈ A then
          (if v ∈ A then y u v else if v = rep then ∑ x ∈ B, y u x else 0)
        else if u = rep then (if v ∈ A then ∑ x ∈ B, y x v else 0) else 0) ∧
      Feas (insert rep A) yc ∧ Even (insert rep A).card ∧
      (insert rep A).card = A.card + 1 := by
  classical
  obtain ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ := hfeas
  have hrepA : rep ∉ A := fun h => (Finset.disjoint_left.mp hdisj) h hrep
  have hAW : A ⊆ W := by rw [hpart]; exact Finset.subset_union_left
  have hBW : B ⊆ W := by rw [hpart]; exact Finset.subset_union_right
  obtain ⟨yc, hyc⟩ : ∃ yc : Fin n → Fin n → ℝ, ∀ u v, yc u v
      = if u ∈ A then
          (if v ∈ A then y u v else if v = rep then ∑ x ∈ B, y u x else 0)
        else if u = rep then (if v ∈ A then ∑ x ∈ B, y x v else 0) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hcardA : (insert rep A).card = A.card + 1 :=
    Finset.card_insert_of_notMem hrepA
  have heven : Even (insert rep A).card := by
    obtain ⟨r, hr⟩ := hAodd
    exact ⟨r + 1, by omega⟩
  -- row sums over `Fin n` restricted to `W`
  have hrowW : ∀ v, ∑ u, y v u = ∑ u ∈ W, y v u := by
    intro v
    refine (Finset.sum_subset (Finset.subset_univ W) (fun x _ hx => ?_)).symm
    by_contra h0
    exact hx (hsupp v x h0).2
  have hsplit : ∀ v, ∑ u ∈ W, y v u = ∑ u ∈ A, y v u + ∑ u ∈ B, y v u := by
    intro v
    rw [hpart, Finset.sum_union hdisj]
  -- closed-form evaluations of `yc`
  have hyAA : ∀ u v, u ∈ A → v ∈ A → yc u v = y u v := by
    intro u v huA hvA
    rw [hyc u v, if_pos huA, if_pos hvA]
  have hyAr : ∀ u, u ∈ A → yc u rep = ∑ x ∈ B, y u x := by
    intro u huA
    rw [hyc u rep, if_pos huA, if_neg hrepA, if_pos rfl]
  have hyrA : ∀ v, v ∈ A → yc rep v = ∑ x ∈ B, y x v := by
    intro v hvA
    rw [hyc rep v, if_neg hrepA, if_pos rfl, if_pos hvA]
  have hyA0 : ∀ u v, u ∈ A → v ∉ A → v ≠ rep → yc u v = 0 := by
    intro u v huA hvA hvr
    rw [hyc u v, if_pos huA, if_neg hvA, if_neg hvr]
  have hy0 : ∀ u v, u ∉ A → u ≠ rep → yc u v = 0 := by
    intro u v huA hur
    rw [hyc u v, if_neg huA, if_neg hur]
  have hyr0 : ∀ v, v ∉ A → yc rep v = 0 := by
    intro v hvA
    rw [hyc rep v, if_neg hrepA, if_pos rfl, if_neg hvA]
  have hycsym : ∀ u v, yc u v = yc v u := by
    intro u v
    by_cases huA : u ∈ A <;> by_cases hvA : v ∈ A
    · rw [hyAA u v huA hvA, hyAA v u hvA huA, hsym]
    · by_cases hvr : v = rep
      · rw [hvr, hyAr u huA, hyrA u huA]
        exact Finset.sum_congr rfl (fun x _ => hsym u x)
      · rw [hyA0 u v huA hvA hvr, hy0 v u hvA hvr]
    · by_cases hur : u = rep
      · rw [hur, hyrA v hvA, hyAr v hvA]
        exact Finset.sum_congr rfl (fun x _ => hsym x v)
      · rw [hy0 u v huA hur, hyA0 v u hvA huA hur]
    · by_cases hur : u = rep
      · rw [hur]
        by_cases hvr : v = rep
        · rw [hvr]
        · rw [hyr0 v hvA, hy0 v rep hvA hvr]
      · by_cases hvr : v = rep
        · rw [hvr, hy0 u rep huA hur, hyr0 u huA]
        · rw [hy0 u v huA hur, hy0 v u hvA hvr]
  refine ⟨yc, hyc, ⟨hycsym, ?_, ?_, ?_, ?_, ?_⟩, heven, hcardA⟩
  · -- nonnegativity
    intro u v
    rw [hyc u v]
    by_cases huA : u ∈ A
    · rw [if_pos huA]
      by_cases hvA : v ∈ A
      · rw [if_pos hvA]; exact hnn u v
      · rw [if_neg hvA]
        by_cases hvr : v = rep
        · rw [if_pos hvr]
          exact Finset.sum_nonneg (fun x _ => hnn u x)
        · rw [if_neg hvr]
    · rw [if_neg huA]
      by_cases hur : u = rep
      · rw [if_pos hur]
        by_cases hvA : v ∈ A
        · rw [if_pos hvA]
          exact Finset.sum_nonneg (fun x _ => hnn x v)
        · rw [if_neg hvA]
      · rw [if_neg hur]
  · -- diagonal
    intro v
    rw [hyc v v]
    by_cases hvA : v ∈ A
    · rw [if_pos hvA, if_pos hvA]
      exact hdiag v
    · rw [if_neg hvA]
      by_cases hvr : v = rep
      · rw [if_pos hvr, if_neg hvA]
      · rw [if_neg hvr]
  · -- support
    intro u v h0
    rw [hyc u v] at h0
    by_cases huA : u ∈ A
    · rw [if_pos huA] at h0
      refine ⟨Finset.mem_insert_of_mem huA, ?_⟩
      by_cases hvA : v ∈ A
      · exact Finset.mem_insert_of_mem hvA
      · rw [if_neg hvA] at h0
        by_cases hvr : v = rep
        · rw [hvr]; exact Finset.mem_insert_self rep A
        · rw [if_neg hvr] at h0
          norm_num at h0
    · rw [if_neg huA] at h0
      by_cases hur : u = rep
      · rw [if_pos hur] at h0
        refine ⟨by rw [hur]; exact Finset.mem_insert_self rep A, ?_⟩
        by_cases hvA : v ∈ A
        · exact Finset.mem_insert_of_mem hvA
        · rw [if_neg hvA] at h0
          norm_num at h0
      · rw [if_neg hur] at h0
        norm_num at h0
  · -- degrees
    intro v hv
    rcases Finset.mem_insert.mp hv with hvr | hvA
    · -- v = rep : the tight cut supplies degree one
      have hpt : ∀ u : Fin n, yc rep u = if u ∈ A then ∑ x ∈ B, y x u else 0 := by
        intro u
        rw [hyc rep u, if_neg hrepA, if_pos rfl]
      rw [hvr, Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hpt u),
        Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_comm]
      rw [← htight]
      exact cut_swap y hsym B A
    · have hpt : ∀ u : Fin n, yc v u
          = (if u ∈ A then y v u else 0) + (if u = rep then ∑ x ∈ B, y v x else 0) := by
        intro u
        rw [hyc v u, if_pos hvA]
        by_cases huA : u ∈ A
        · rw [if_pos huA, if_pos huA,
            if_neg (fun h : u = rep => hrepA (h ▸ huA))]
          ring
        · rw [if_neg huA, if_neg huA]
          by_cases hur : u = rep
          · rw [if_pos hur]
            ring
          · rw [if_neg hur]
            ring
      rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hpt u),
        Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
        Finset.sum_ite_eq' Finset.univ rep (fun _ => ∑ x ∈ B, y v x),
        if_pos (Finset.mem_univ rep)]
      have h1 := hdeg v (hAW hvA)
      rw [hrowW v, hsplit v] at h1
      linarith
  · -- odd cuts
    have hmain : ∀ S' : Finset (Fin n), S' ⊆ insert rep A → Odd S'.card →
        rep ∉ S' → 1 ≤ ∑ u ∈ S', ∑ v ∈ insert rep A \ S', yc u v := by
      intro S' hS' hS'odd hrS'
      have hS'A : S' ⊆ A := by
        intro x hx
        rcases Finset.mem_insert.mp (hS' hx) with h | h
        · exact absurd (h ▸ hx) hrS'
        · exact h
      have hins : insert rep A \ S' = insert rep (A \ S') := by
        ext x
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert,
          Finset.mem_sdiff]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · exact ⟨Or.inl h1, fun hc => hrS' (h1 ▸ hc)⟩
          · exact ⟨Or.inr h1, h2⟩
      have hrAS : rep ∉ A \ S' := fun h => hrepA (Finset.mem_sdiff.mp h).1
      have hWsplit : W \ S' = (A \ S') ∪ B := by
        ext x
        rw [Finset.mem_sdiff, hpart, Finset.mem_union, Finset.mem_union,
          Finset.mem_sdiff]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr h1
        · rintro (⟨h1, h2⟩ | h1)
          · exact ⟨Or.inl h1, h2⟩
          · exact ⟨Or.inr h1,
              fun hc => (Finset.disjoint_left.mp hdisj) (hS'A hc) h1⟩
      have hdisj2 : Disjoint (A \ S') B :=
        Finset.disjoint_of_subset_left Finset.sdiff_subset hdisj
      have hinner : ∀ u ∈ S', ∑ v ∈ insert rep A \ S', yc u v
          = ∑ v ∈ W \ S', y u v := by
        intro u hu
        have huA := hS'A hu
        rw [hins, Finset.sum_insert hrAS]
        have h1 : yc u rep = ∑ x ∈ B, y u x := by
          rw [hyc u rep, if_pos huA, if_neg hrepA, if_pos rfl]
        have h2 : ∑ v ∈ A \ S', yc u v = ∑ v ∈ A \ S', y u v :=
          Finset.sum_congr rfl (fun v hv => by
            rw [hyc u v, if_pos huA, if_pos (Finset.mem_sdiff.mp hv).1])
        rw [h1, h2, hWsplit, Finset.sum_union hdisj2]
        ring
      rw [Finset.sum_congr rfl (fun u hu => hinner u hu)]
      exact hodd S' (fun x hx => hAW (hS'A hx)) hS'odd
    intro S' hS' hS'odd
    by_cases hrS' : rep ∈ S'
    · -- pass to the complement inside `insert rep A`
      set T' := insert rep A \ S' with hT'def
      have hT'sub : T' ⊆ insert rep A := Finset.sdiff_subset
      have hrT' : rep ∉ T' := fun h => (Finset.mem_sdiff.mp h).2 hrS'
      have hT'card : Odd T'.card := by
        have h1 : T'.card = (insert rep A).card - S'.card := by
          rw [hT'def, Finset.card_sdiff, Finset.inter_eq_left.mpr hS']
        have h2 : S'.card ≤ (insert rep A).card := Finset.card_le_card hS'
        obtain ⟨r, hr⟩ := heven
        obtain ⟨t, ht⟩ := hS'odd
        exact ⟨r - t - 1, by omega⟩
      have hcompl : insert rep A \ T' = S' := by
        rw [hT'def, Finset.sdiff_sdiff_self_left,
          Finset.inter_eq_right.mpr hS']
      have h1 := hmain T' hT'sub hT'card hrT'
      rw [hcompl] at h1
      calc (1 : ℝ) ≤ ∑ u ∈ T', ∑ v ∈ S', yc u v := h1
        _ = ∑ u ∈ S', ∑ v ∈ T', yc u v := cut_swap yc hycsym T' S'
    · exact hmain S' hS' hS'odd hrS'

/-! ### Handler 2: contracting a nontrivial tight odd cut and gluing -/

lemma decomp_contract (N : ℕ)
    (oracle : ∀ (W' : Finset (Fin n)) (y' : Fin n → Fin n → ℝ),
      W'.card ≤ N → Even W'.card → Feas W' y' → ∃ L, IsDecomp W' y' L)
    (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ)
    (hcard : W.card ≤ N + 2) (hW : Even W.card) (hfeas : Feas W y)
    (S : Finset (Fin n)) (hSW : S ⊆ W) (hSodd : Odd S.card)
    (hS3 : 3 ≤ S.card) (hS3' : S.card + 3 ≤ W.card)
    (htight : ∑ u ∈ S, ∑ v ∈ W \ S, y u v = 1) :
    ∃ L, IsDecomp W y L := by
  classical
  obtain ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ := hfeas
  set R := W \ S with hRdef
  have hpartS : W = R ∪ S := (Finset.sdiff_union_of_subset hSW).symm
  have hdisjRS : Disjoint R S := Finset.sdiff_disjoint
  have hcardS : S.card ≤ W.card := Finset.card_le_card hSW
  have hcardR : R.card = W.card - S.card := by
    rw [hRdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hSW]
  have hRodd : Odd R.card := by
    obtain ⟨r, hr⟩ := hW
    obtain ⟨t, ht⟩ := hSodd
    exact ⟨r - t - 1, by omega⟩
  obtain ⟨sstar, hsstar⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  obtain ⟨tstar, htstar⟩ := Finset.card_pos.mp
    (show 0 < R.card by rw [hcardR]; omega)
  have hsstarR : sstar ∉ R := fun h => (Finset.disjoint_left.mp hdisjRS) h hsstar
  have htstarS : tstar ∉ S := fun h => (Finset.disjoint_left.mp hdisjRS) htstar h
  have htight2 : ∑ u ∈ S, ∑ v ∈ R, y u v = 1 := htight
  have htight1 : ∑ u ∈ R, ∑ v ∈ S, y u v = 1 := by
    rw [cut_swap y hsym R S]
    exact htight2
  obtain ⟨y₁, hy₁, hfeas₁, heven₁, hcard₁⟩ :=
    contract_feas W y ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ R S hpartS hdisjRS
      hRodd sstar hsstar htight1
  have hpartR : W = S ∪ R := by rw [hpartS, Finset.union_comm]
  obtain ⟨y₂, hy₂, hfeas₂, heven₂, hcard₂⟩ :=
    contract_feas W y ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ S R hpartR
      hdisjRS.symm hSodd tstar htstar htight2
  obtain ⟨L₁, hL₁ne, hL₁mem, hL₁sum, hL₁dec⟩ := oracle (insert sstar R) y₁
    (by rw [hcard₁, hcardR]; omega) heven₁ hfeas₁
  obtain ⟨L₂, hL₂ne, hL₂mem, hL₂sum, hL₂dec⟩ := oracle (insert tstar S) y₂
    (by rw [hcard₂]; omega) heven₂ hfeas₂
  -- pairings send the representatives into the opposite side
  have hpair₁ : ∀ p ∈ L₁, p.2 sstar ∈ R ∧ p.2 (p.2 sstar) = sstar := by
    intro p hp
    obtain ⟨-, hpair, -⟩ := hL₁mem p hp
    obtain ⟨h1, h2, h3⟩ := hpair sstar (Finset.mem_insert_self _ _)
    refine ⟨?_, h2⟩
    rcases Finset.mem_insert.mp h1 with h | h
    · exact absurd h h3
    · exact h
  have hpair₂ : ∀ q ∈ L₂, q.2 tstar ∈ S ∧ q.2 (q.2 tstar) = tstar := by
    intro q hq
    obtain ⟨-, hpair, -⟩ := hL₂mem q hq
    obtain ⟨h1, h2, h3⟩ := hpair tstar (Finset.mem_insert_self _ _)
    refine ⟨?_, h2⟩
    rcases Finset.mem_insert.mp h1 with h | h
    · exact absurd h h3
    · exact h
  -- closed forms of the contracted rows
  have hαid : ∀ a ∈ R, y₁ sstar a = ∑ x ∈ S, y x a := by
    intro a ha
    rw [hy₁ sstar a, if_neg hsstarR, if_pos rfl, if_pos ha]
  have hα0 : ∀ a, a ∉ R → y₁ sstar a = 0 := by
    intro a ha
    rw [hy₁ sstar a, if_neg hsstarR, if_pos rfl, if_neg ha]
  have hβid : ∀ b ∈ S, y₂ tstar b = ∑ x ∈ R, y x b := by
    intro b hb
    rw [hy₂ tstar b, if_neg htstarS, if_pos rfl, if_pos hb]
  have hβ0 : ∀ b, b ∉ S → y₂ tstar b = 0 := by
    intro b hb
    rw [hy₂ tstar b, if_neg htstarS, if_pos rfl, if_neg hb]
  -- dominations
  have hdomα : ∀ a ∈ R, ∀ b ∈ S, y a b ≤ y₁ sstar a := by
    intro a ha b hb
    rw [hαid a ha, hsym a b]
    exact Finset.single_le_sum (fun x _ => hnn x a) hb
  have hdomβ : ∀ a ∈ R, ∀ b ∈ S, y a b ≤ y₂ tstar b := by
    intro a ha b hb
    rw [hβid b hb]
    exact Finset.single_le_sum (fun x _ => hnn x b) ha
  -- marginals of the decompositions
  have hmarg₁ : ∀ a, (L₁.map (fun p => if p.2 sstar = a then p.1 else 0)).sum
      = y₁ sstar a := by
    intro a
    rw [hL₁dec sstar a]
    exact list_sum_congr _ _ _ (fun p _ => by
      by_cases h : p.2 sstar = a
      · rw [if_pos h, if_pos ⟨h, Finset.mem_insert_self _ _⟩]
      · rw [if_neg h, if_neg (fun hh => h hh.1)])
  have hmarg₂ : ∀ b, (L₂.map (fun q => if q.2 tstar = b then q.1 else 0)).sum
      = y₂ tstar b := by
    intro b
    rw [hL₂dec tstar b]
    exact list_sum_congr _ _ _ (fun q _ => by
      by_cases h : q.2 tstar = b
      · rw [if_pos h, if_pos ⟨h, Finset.mem_insert_self _ _⟩]
      · rw [if_neg h, if_neg (fun hh => h hh.1)])
  -- positivity of the conditioning masses
  have hαpos : ∀ p ∈ L₁, 0 < y₁ sstar (p.2 sstar) := by
    intro p hp
    have h1 : p.1 ≤ (L₁.map (fun p' =>
        if p'.2 sstar = p.2 sstar then p'.1 else 0)).sum := by
      have h2 := list_sum_single_le L₁
        (fun p' => if p'.2 sstar = p.2 sstar then p'.1 else 0) p hp
        (fun p' hp' => by
          show 0 ≤ if p'.2 sstar = p.2 sstar then p'.1 else 0
          by_cases h : p'.2 sstar = p.2 sstar
          · rw [if_pos h]
            exact le_of_lt (hL₁mem p' hp').1
          · rw [if_neg h])
      have h3 : (if p.2 sstar = p.2 sstar then p.1 else 0)
          ≤ (L₁.map (fun p' => if p'.2 sstar = p.2 sstar then p'.1 else 0)).sum := h2
      rw [if_pos rfl] at h3
      exact h3
    rw [hmarg₁ (p.2 sstar)] at h1
    exact lt_of_lt_of_le (hL₁mem p hp).1 h1
  have hβpos : ∀ q ∈ L₂, 0 < y₂ tstar (q.2 tstar) := by
    intro q hq
    have h1 : q.1 ≤ (L₂.map (fun q' =>
        if q'.2 tstar = q.2 tstar then q'.1 else 0)).sum := by
      have h2 := list_sum_single_le L₂
        (fun q' => if q'.2 tstar = q.2 tstar then q'.1 else 0) q hq
        (fun q' hq' => by
          show 0 ≤ if q'.2 tstar = q.2 tstar then q'.1 else 0
          by_cases h : q'.2 tstar = q.2 tstar
          · rw [if_pos h]
            exact le_of_lt (hL₂mem q' hq').1
          · rw [if_neg h])
      have h3 : (if q.2 tstar = q.2 tstar then q.1 else 0)
          ≤ (L₂.map (fun q' => if q'.2 tstar = q.2 tstar then q'.1 else 0)).sum := h2
      rw [if_pos rfl] at h3
      exact h3
    rw [hmarg₂ (q.2 tstar)] at h1
    exact lt_of_lt_of_le (hL₂mem q hq).1 h1
  -- the coupling weights and merged pairings
  obtain ⟨ν, hν⟩ : ∃ f : (ℝ × (Fin n → Fin n)) → (ℝ × (Fin n → Fin n)) → ℝ,
      ∀ p q, f p q = p.1 * q.1 * y (p.2 sstar) (q.2 tstar)
        / (y₁ sstar (p.2 sstar) * y₂ tstar (q.2 tstar)) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨mg, hmg⟩ : ∃ F : (Fin n → Fin n) → (Fin n → Fin n) → (Fin n → Fin n),
      ∀ A' B' x, F A' B' x = if x = A' sstar then B' tstar
        else if x = B' tstar then A' sstar
        else if x ∈ S then B' x else if x ∈ R then A' x else x :=
    ⟨_, fun _ _ _ => rfl⟩
  have hνnn : ∀ p ∈ L₁, ∀ q ∈ L₂, 0 ≤ ν p q := by
    intro p hp q hq
    rw [hν]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (le_of_lt (hL₁mem p hp).1)
        (le_of_lt (hL₂mem q hq).1)) (hnn _ _))
      (le_of_lt (mul_pos (hαpos p hp) (hβpos q hq)))
  -- the two conditional-sum identities
  have hinner : ∀ p ∈ L₁, (L₂.map (fun q => ν p q)).sum = p.1 := by
    intro p hp
    have ha := (hpair₁ p hp).1
    have hαp := hαpos p hp
    rw [list_sum_congr _ _ (fun q => q.1 * (fun b => p.1 * y (p.2 sstar) b
        / (y₁ sstar (p.2 sstar) * y₂ tstar b)) (q.2 tstar))
      (fun q _ => by rw [hν]; ring),
      list_group L₂ (fun g => g tstar)
        (fun b => p.1 * y (p.2 sstar) b
          / (y₁ sstar (p.2 sstar) * y₂ tstar b))]
    have hptb : ∀ b : Fin n, y₂ tstar b * (p.1 * y (p.2 sstar) b
        / (y₁ sstar (p.2 sstar) * y₂ tstar b))
        = if b ∈ S then p.1 * y (p.2 sstar) b / y₁ sstar (p.2 sstar) else 0 := by
      intro b
      by_cases hbS : b ∈ S
      · rw [if_pos hbS]
        by_cases hb0 : y₂ tstar b = 0
        · have hyab : y (p.2 sstar) b = 0 := by
            have h1 := hdomβ (p.2 sstar) ha b hbS
            have h2 := hnn (p.2 sstar) b
            rw [hb0] at h1
            linarith
          rw [hyab, hb0]
          ring
        · have hα0' : y₁ sstar (p.2 sstar) ≠ 0 := ne_of_gt hαp
          field_simp
      · rw [if_neg hbS, hβ0 b hbS]
        ring
    have step1 : ∑ b, (L₂.map (fun q => if q.2 tstar = b then q.1 else 0)).sum
        * (p.1 * y (p.2 sstar) b / (y₁ sstar (p.2 sstar) * y₂ tstar b))
        = ∑ b, (if b ∈ S then p.1 * y (p.2 sstar) b
            / y₁ sstar (p.2 sstar) else 0) := by
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [hmarg₂ b]
      exact hptb b
    rw [step1, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div,
      ← Finset.mul_sum]
    have hαeq : y₁ sstar (p.2 sstar) = ∑ b ∈ S, y (p.2 sstar) b := by
      rw [hαid _ ha]
      exact Finset.sum_congr rfl (fun x _ => hsym x _)
    rw [← hαeq, mul_div_assoc, div_self (ne_of_gt hαp), mul_one]
  have hinner' : ∀ q ∈ L₂, (L₁.map (fun p => ν p q)).sum = q.1 := by
    intro q hq
    have hb := (hpair₂ q hq).1
    have hβq := hβpos q hq
    rw [list_sum_congr _ _ (fun p => p.1 * (fun a => q.1 * y a (q.2 tstar)
        / (y₁ sstar a * y₂ tstar (q.2 tstar))) (p.2 sstar))
      (fun p _ => by rw [hν]; ring),
      list_group L₁ (fun g => g sstar)
        (fun a => q.1 * y a (q.2 tstar)
          / (y₁ sstar a * y₂ tstar (q.2 tstar)))]
    have hpta : ∀ a : Fin n, y₁ sstar a * (q.1 * y a (q.2 tstar)
        / (y₁ sstar a * y₂ tstar (q.2 tstar)))
        = if a ∈ R then q.1 * y a (q.2 tstar) / y₂ tstar (q.2 tstar) else 0 := by
      intro a
      by_cases haR : a ∈ R
      · rw [if_pos haR]
        by_cases ha0 : y₁ sstar a = 0
        · have hyab : y a (q.2 tstar) = 0 := by
            have h1 := hdomα a haR (q.2 tstar) hb
            have h2 := hnn a (q.2 tstar)
            rw [ha0] at h1
            linarith
          rw [hyab, ha0]
          ring
        · have hβ0' : y₂ tstar (q.2 tstar) ≠ 0 := ne_of_gt hβq
          field_simp
      · rw [if_neg haR, hα0 a haR]
        ring
    have step1 : ∑ a, (L₁.map (fun p => if p.2 sstar = a then p.1 else 0)).sum
        * (q.1 * y a (q.2 tstar) / (y₁ sstar a * y₂ tstar (q.2 tstar)))
        = ∑ a, (if a ∈ R then q.1 * y a (q.2 tstar)
            / y₂ tstar (q.2 tstar) else 0) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [hmarg₁ a]
      exact hpta a
    rw [step1, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div,
      ← Finset.mul_sum]
    have hβeq : y₂ tstar (q.2 tstar) = ∑ a ∈ R, y a (q.2 tstar) :=
      hβid _ hb
    rw [← hβeq, mul_div_assoc, div_self (ne_of_gt hβq), mul_one]
  -- evaluations and involution facts for the merged pairing
  have hmgaP : ∀ p q : ℝ × (Fin n → Fin n), mg p.2 q.2 (p.2 sstar) = q.2 tstar := by
    intro p q
    rw [hmg, if_pos rfl]
  have habP : ∀ p ∈ L₁, ∀ q ∈ L₂, p.2 sstar ≠ q.2 tstar := by
    intro p hp q hq h
    exact (Finset.disjoint_left.mp hdisjRS) (hpair₁ p hp).1 (h ▸ (hpair₂ q hq).1)
  have hmgbP : ∀ p ∈ L₁, ∀ q ∈ L₂, mg p.2 q.2 (q.2 tstar) = p.2 sstar := by
    intro p hp q hq
    rw [hmg, if_neg (fun h => habP p hp q hq h.symm), if_pos rfl]
  have hmgSP : ∀ p ∈ L₁, ∀ q : ℝ × (Fin n → Fin n), ∀ x ∈ S, x ≠ q.2 tstar →
      mg p.2 q.2 x = q.2 x := by
    intro p hp q x hxS hxb
    rw [hmg, if_neg (fun h => (Finset.disjoint_left.mp hdisjRS)
      (hpair₁ p hp).1 (by rw [← h]; exact hxS)), if_neg hxb, if_pos hxS]
  have hmgRP : ∀ p : ℝ × (Fin n → Fin n), ∀ q ∈ L₂, ∀ x ∈ R, x ≠ p.2 sstar →
      mg p.2 q.2 x = p.2 x := by
    intro p q hq x hxR hxa
    rw [hmg, if_neg hxa,
      if_neg (fun h => (Finset.disjoint_left.mp hdisjRS) hxR
        (by rw [h]; exact (hpair₂ q hq).1)),
      if_neg (fun h => (Finset.disjoint_left.mp hdisjRS) hxR h), if_pos hxR]
  have hAact : ∀ p ∈ L₁, ∀ x ∈ R, x ≠ p.2 sstar →
      p.2 x ∈ R ∧ p.2 (p.2 x) = x ∧ p.2 x ≠ x ∧ p.2 x ≠ p.2 sstar := by
    intro p hp x hxR hxa
    obtain ⟨-, hApair, -⟩ := hL₁mem p hp
    obtain ⟨h1, h2, h3⟩ := hApair x (Finset.mem_insert_of_mem hxR)
    have h4 : p.2 x ≠ sstar := fun h => hxa (by rw [← h2, h])
    have h5 : p.2 x ∈ R := by
      rcases Finset.mem_insert.mp h1 with h | h
      · exact absurd h h4
      · exact h
    have h6 : p.2 x ≠ p.2 sstar := by
      intro h
      have h7 := h2
      rw [h, (hpair₁ p hp).2] at h7
      exact hsstarR (h7 ▸ hxR)
    exact ⟨h5, h2, h3, h6⟩
  have hBact : ∀ q ∈ L₂, ∀ x ∈ S, x ≠ q.2 tstar →
      q.2 x ∈ S ∧ q.2 (q.2 x) = x ∧ q.2 x ≠ x ∧ q.2 x ≠ q.2 tstar := by
    intro q hq x hxS hxb
    obtain ⟨-, hBpair, -⟩ := hL₂mem q hq
    obtain ⟨h1, h2, h3⟩ := hBpair x (Finset.mem_insert_of_mem hxS)
    have h4 : q.2 x ≠ tstar := fun h => hxb (by rw [← h2, h])
    have h5 : q.2 x ∈ S := by
      rcases Finset.mem_insert.mp h1 with h | h
      · exact absurd h h4
      · exact h
    have h6 : q.2 x ≠ q.2 tstar := by
      intro h
      have h7 := h2
      rw [h, (hpair₂ q hq).2] at h7
      exact htstarS (h7 ▸ hxS)
    exact ⟨h5, h2, h3, h6⟩
  have hRW : R ⊆ W := by rw [hpartS]; exact Finset.subset_union_left
  have hmgW : ∀ p ∈ L₁, ∀ q ∈ L₂, ∀ x ∈ W, mg p.2 q.2 x ∈ W := by
    intro p hp q hq x hxW
    have hxRS : x ∈ R ∨ x ∈ S := by
      rw [hpartS] at hxW
      exact Finset.mem_union.mp hxW
    by_cases hxa : x = p.2 sstar
    · rw [hxa, hmgaP p q]
      exact hSW (hpair₂ q hq).1
    · by_cases hxb : x = q.2 tstar
      · rw [hxb, hmgbP p hp q hq]
        exact hRW (hpair₁ p hp).1
      · rcases hxRS with hxR | hxS
        · rw [hmgRP p q hq x hxR hxa]
          exact hRW (hAact p hp x hxR hxa).1
        · rw [hmgSP p hp q x hxS hxb]
          exact hSW (hBact q hq x hxS hxb).1
  have hmgpair : ∀ p ∈ L₁, ∀ q ∈ L₂,
      (∀ v ∈ W, mg p.2 q.2 v ∈ W ∧ mg p.2 q.2 (mg p.2 q.2 v) = v
        ∧ mg p.2 q.2 v ≠ v) ∧ (∀ v ∉ W, mg p.2 q.2 v = v) := by
    intro p hp q hq
    constructor
    · intro v hv
      refine ⟨hmgW p hp q hq v hv, ?_, ?_⟩
      · by_cases hva : v = p.2 sstar
        · rw [hva, hmgaP p q, hmgbP p hp q hq]
        · by_cases hvb : v = q.2 tstar
          · rw [hvb, hmgbP p hp q hq, hmgaP p q]
          · have hvRS : v ∈ R ∨ v ∈ S := by
              rw [hpartS] at hv
              exact Finset.mem_union.mp hv
            rcases hvRS with hvR | hvS
            · obtain ⟨h5, h2, h3, h6⟩ := hAact p hp v hvR hva
              rw [hmgRP p q hq v hvR hva, hmgRP p q hq (p.2 v) h5 h6, h2]
            · obtain ⟨h5, h2, h3, h6⟩ := hBact q hq v hvS hvb
              rw [hmgSP p hp q v hvS hvb, hmgSP p hp q (q.2 v) h5 h6, h2]
      · by_cases hva : v = p.2 sstar
        · rw [hva, hmgaP p q]
          exact fun h => habP p hp q hq h.symm
        · by_cases hvb : v = q.2 tstar
          · rw [hvb, hmgbP p hp q hq]
            exact fun h => habP p hp q hq h
          · have hvRS : v ∈ R ∨ v ∈ S := by
              rw [hpartS] at hv
              exact Finset.mem_union.mp hv
            rcases hvRS with hvR | hvS
            · rw [hmgRP p q hq v hvR hva]
              exact (hAact p hp v hvR hva).2.2.1
            · rw [hmgSP p hp q v hvS hvb]
              exact (hBact q hq v hvS hvb).2.2.1
    · intro v hv
      rw [hmg,
        if_neg (fun h => hv (by rw [h]; exact hRW (hpair₁ p hp).1)),
        if_neg (fun h => hv (by rw [h]; exact hSW (hpair₂ q hq).1)),
        if_neg (fun h => hv (hSW h)), if_neg (fun h => hv (hRW h))]
  -- the merged list
  set Lraw := L₁.flatMap (fun p => L₂.map (fun q => (ν p q, mg p.2 q.2)))
    with hLraw
  set L := Lraw.filter (fun r => decide (0 < r.1)) with hLdef
  have hLrawmem : ∀ r ∈ Lraw, ∃ p, p ∈ L₁ ∧ ∃ q, q ∈ L₂
      ∧ r = (ν p q, mg p.2 q.2) := by
    intro r hr
    rw [hLraw] at hr
    obtain ⟨p, hp, hr2⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hr2
    exact ⟨p, hp, q, hq, hqe.symm⟩
  have hLrawnn : ∀ r ∈ Lraw, 0 ≤ r.1 := by
    intro r hr
    obtain ⟨p, hp, q, hq, rfl⟩ := hLrawmem r hr
    exact hνnn p hp q hq
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · -- nonemptiness
    obtain ⟨p₀, hp₀⟩ := List.exists_mem_of_ne_nil L₁ hL₁ne
    have ha₀ := (hpair₁ p₀ hp₀).1
    have hα₀ := hαpos p₀ hp₀
    have hex : ∃ b₀ ∈ S, 0 < y (p₀.2 sstar) b₀ := by
      by_contra hno
      push_neg at hno
      have hzero : y₁ sstar (p₀.2 sstar) = 0 := by
        rw [hαid _ ha₀]
        refine Finset.sum_eq_zero (fun x hx => ?_)
        have h1 := hno x hx
        have h2 := hnn (p₀.2 sstar) x
        rw [hsym x _]
        linarith
      rw [hzero] at hα₀
      norm_num at hα₀
    obtain ⟨b₀, hb₀S, hb₀pos⟩ := hex
    have hq₀ex : ∃ q₀ ∈ L₂, q₀.2 tstar = b₀ := by
      by_contra hno
      push_neg at hno
      have h1 : y₂ tstar b₀ = 0 := by
        rw [← hmarg₂ b₀]
        exact list_sum_zero_of_all _ _ (fun q hq => if_neg (hno q hq))
      have h2 := hdomβ _ ha₀ _ hb₀S
      rw [h1] at h2
      linarith
    obtain ⟨q₀, hq₀, hq₀b⟩ := hq₀ex
    have hν₀ : 0 < ν p₀ q₀ := by
      rw [hν]
      apply div_pos
      · apply mul_pos (mul_pos (hL₁mem p₀ hp₀).1 (hL₂mem q₀ hq₀).1)
        rw [hq₀b]
        exact hb₀pos
      · exact mul_pos (hαpos p₀ hp₀) (hβpos q₀ hq₀)
    have hmem : (ν p₀ q₀, mg p₀.2 q₀.2) ∈ L := by
      rw [hLdef]
      refine List.mem_filter.mpr ⟨?_, by simpa using hν₀⟩
      rw [hLraw]
      exact List.mem_flatMap.mpr ⟨p₀, hp₀, List.mem_map.mpr ⟨q₀, hq₀, rfl⟩⟩
    exact List.ne_nil_of_mem hmem
  · -- member properties
    intro r hr
    rw [hLdef] at hr
    obtain ⟨hrRaw, hrpos⟩ := List.mem_filter.mp hr
    obtain ⟨p, hp, q, hq, rfl⟩ := hLrawmem _ hrRaw
    exact ⟨by simpa using hrpos, (hmgpair p hp q hq).1, (hmgpair p hp q hq).2⟩
  · -- total weight
    have h1 : (L.map Prod.fst).sum = (Lraw.map Prod.fst).sum := by
      rw [hLdef]
      exact list_filter_sum Lraw Prod.fst
        (fun r hr h0 => le_antisymm (not_lt.mp h0) (hLrawnn r hr))
    rw [h1, hLraw, list_flatMap_sum,
      list_sum_congr _ _ (fun p => (L₂.map (fun q => ν p q)).sum) (fun p hp => by
        rw [List.map_map]
        exact list_sum_congr _ _ _ (fun q _ => rfl)),
      list_sum_congr _ _ Prod.fst (fun p hp => hinner p hp)]
    exact hL₁sum
  · -- the decomposition equation
    intro u v
    have hLL : (L.map (fun r => if r.2 u = v ∧ u ∈ W then r.1 else 0)).sum
        = (Lraw.map (fun r => if r.2 u = v ∧ u ∈ W then r.1 else 0)).sum := by
      rw [hLdef]
      refine list_filter_sum Lraw _ (fun r hr h0 => ?_)
      have h1 : r.1 = 0 := le_antisymm (not_lt.mp h0) (hLrawnn r hr)
      by_cases h : r.2 u = v ∧ u ∈ W
      · rw [if_pos h, h1]
      · rw [if_neg h]
    rw [hLL, hLraw, list_flatMap_sum,
      list_sum_congr _ _ (fun p => (L₂.map (fun q =>
        if mg p.2 q.2 u = v ∧ u ∈ W then ν p q else 0)).sum) (fun p hp => by
        rw [List.map_map]
        exact list_sum_congr _ _ _ (fun q _ => rfl))]
    by_cases huW : u ∈ W
    swap
    · have hy0' : y u v = 0 := by
        by_contra h0
        exact huW (hsupp u v h0).1
      rw [hy0']
      symm
      exact list_sum_zero_of_all _ _ (fun p hp =>
        list_sum_zero_of_all _ _ (fun q hq => if_neg (fun hh => huW hh.2)))
    rw [list_sum_congr _ _ (fun p => (L₂.map (fun q =>
        if mg p.2 q.2 u = v then ν p q else 0)).sum) (fun p hp =>
      list_sum_congr _ _ _ (fun q hq => by
        by_cases h : mg p.2 q.2 u = v
        · rw [if_pos ⟨h, huW⟩, if_pos h]
        · rw [if_neg (fun hh => h hh.1), if_neg h]))]
    have huRS : u ∈ R ∨ u ∈ S := by
      rw [hpartS] at huW
      exact Finset.mem_union.mp huW
    by_cases hvW : v ∈ W
    swap
    · -- v outside W : nothing matches
      have hy0' : y u v = 0 := by
        by_contra h0
        exact hvW (hsupp u v h0).2
      rw [hy0']
      symm
      refine list_sum_zero_of_all _ _ (fun p hp =>
        list_sum_zero_of_all _ _ (fun q hq =>
          if_neg (fun hh => hvW (by rw [← hh]; exact hmgW p hp q hq u huW))))
    have hvRS : v ∈ R ∨ v ∈ S := by
      rw [hpartS] at hvW
      exact Finset.mem_union.mp hvW
    rcases huRS with huR | huS
    · rcases hvRS with hvR | hvS
      · -- u ∈ R, v ∈ R : the kept side of instance 1
        have hstep : ∀ p ∈ L₁, (L₂.map (fun q =>
            if mg p.2 q.2 u = v then ν p q else 0)).sum
            = if p.2 u = v then p.1 else 0 := by
          intro p hp
          by_cases hua : u = p.2 sstar
          · have h1 : (L₂.map (fun q =>
                if mg p.2 q.2 u = v then ν p q else 0)).sum = 0 :=
              list_sum_zero_of_all _ _ (fun q hq => by
                rw [hua, hmgaP p q]
                exact if_neg (fun hh => (Finset.disjoint_left.mp hdisjRS)
                  hvR (by rw [← hh]; exact (hpair₂ q hq).1)))
            rw [h1, if_neg (fun hh => ?_)]
            rw [hua, (hpair₁ p hp).2] at hh
            exact hsstarR (by rw [hh]; exact hvR)
          · have h2 : ∀ q ∈ L₂, (if mg p.2 q.2 u = v then ν p q else 0)
                = if p.2 u = v then ν p q else 0 := by
              intro q hq
              rw [hmgRP p q hq u huR hua]
            rw [list_sum_congr _ _ _ h2]
            by_cases hpu : p.2 u = v
            · rw [if_pos hpu, list_sum_congr _ _ (fun q => ν p q)
                (fun q hq => if_pos hpu)]
              exact hinner p hp
            · rw [if_neg hpu]
              exact list_sum_zero_of_all _ _ (fun q hq => if_neg hpu)
        have hfin : (L₁.map (fun p => if p.2 u = v then p.1 else 0)).sum
            = y₁ u v := by
          rw [hL₁dec u v]
          exact list_sum_congr _ _ _ (fun p _ => by
            by_cases h : p.2 u = v
            · rw [if_pos h, if_pos ⟨h, Finset.mem_insert_of_mem huR⟩]
            · rw [if_neg h, if_neg (fun hh => h hh.1)])
        rw [list_sum_congr _ _ _ hstep, hfin, hy₁ u v, if_pos huR, if_pos hvR]
      · -- u ∈ R, v ∈ S : the crossing pair
        have hstep : ∀ p ∈ L₁, (L₂.map (fun q =>
            if mg p.2 q.2 u = v then ν p q else 0)).sum
            = (if p.2 sstar = u then p.1 else 0)
              * (y₂ tstar v * (y u v / (y₁ sstar u * y₂ tstar v))) := by
          intro p hp
          by_cases hua : u = p.2 sstar
          · have h2 : ∀ q ∈ L₂, (if mg p.2 q.2 u = v then ν p q else 0)
                = (if q.2 tstar = v then q.1 else 0)
                  * (p.1 * (y u v / (y₁ sstar u * y₂ tstar v))) := by
              intro q hq
              rw [hua, hmgaP p q]
              by_cases h : q.2 tstar = v
              · rw [if_pos h, if_pos h, hν, ← hua, h]
                ring
              · rw [if_neg h, if_neg h]
                ring
            rw [list_sum_congr _ _ _ h2, list_sum_scale_right, hmarg₂ v,
              if_pos hua.symm]
            ring
          · have h2 : (L₂.map (fun q =>
                if mg p.2 q.2 u = v then ν p q else 0)).sum = 0 :=
              list_sum_zero_of_all _ _ (fun q hq => by
                rw [hmgRP p q hq u huR hua]
                exact if_neg (fun hh => (Finset.disjoint_left.mp hdisjRS)
                  (hAact p hp u huR hua).1 (by rw [hh]; exact hvS)))
            rw [h2, if_neg (fun hh => hua hh.symm)]
            ring
        rw [list_sum_congr _ _ _ hstep, list_sum_scale_right, hmarg₁ u]
        by_cases hz1 : y₁ sstar u = 0
        · have h1 := hdomα u huR v hvS
          have h2 := hnn u v
          rw [hz1] at h1 ⊢
          have h3 : y u v = 0 := le_antisymm h1 h2
          rw [h3]
          ring
        · by_cases hz2 : y₂ tstar v = 0
          · have h1 := hdomβ u huR v hvS
            have h2 := hnn u v
            rw [hz2] at h1 ⊢
            have h3 : y u v = 0 := le_antisymm h1 h2
            rw [h3]
            ring
          · field_simp
    · rcases hvRS with hvR | hvS
      · -- u ∈ S, v ∈ R : the crossing pair, reversed
        have hstep : ∀ p ∈ L₁, (L₂.map (fun q =>
            if mg p.2 q.2 u = v then ν p q else 0)).sum
            = (if p.2 sstar = v then p.1 else 0)
              * (y₂ tstar u * (y v u / (y₁ sstar v * y₂ tstar u))) := by
          intro p hp
          by_cases hpv : p.2 sstar = v
          · have h2 : ∀ q ∈ L₂, (if mg p.2 q.2 u = v then ν p q else 0)
                = (if q.2 tstar = u then q.1 else 0)
                  * (p.1 * (y v u / (y₁ sstar v * y₂ tstar u))) := by
              intro q hq
              by_cases hub : u = q.2 tstar
              · rw [hub, hmgbP p hp q hq, if_pos hpv, if_pos rfl, hν, hpv]
                ring
              · rw [hmgSP p hp q u huS hub,
                  if_neg (fun hh => (Finset.disjoint_left.mp hdisjRS) hvR
                    (by rw [← hh]; exact (hBact q hq u huS hub).1)),
                  if_neg (fun hh => hub hh.symm)]
                ring
            rw [list_sum_congr _ _ _ h2, list_sum_scale_right, hmarg₂ u,
              if_pos hpv]
            ring
          · have h2 : (L₂.map (fun q =>
                if mg p.2 q.2 u = v then ν p q else 0)).sum = 0 :=
              list_sum_zero_of_all _ _ (fun q hq => by
                by_cases hub : u = q.2 tstar
                · rw [hub, hmgbP p hp q hq]
                  exact if_neg hpv
                · rw [hmgSP p hp q u huS hub]
                  exact if_neg (fun hh => (Finset.disjoint_left.mp hdisjRS) hvR
                    (by rw [← hh]; exact (hBact q hq u huS hub).1)))
            rw [h2, if_neg hpv]
            ring
        rw [list_sum_congr _ _ _ hstep, list_sum_scale_right, hmarg₁ v,
          hsym u v]
        by_cases hz1 : y₁ sstar v = 0
        · have h1 := hdomα v hvR u huS
          have h2 := hnn v u
          rw [hz1] at h1 ⊢
          have h3 : y v u = 0 := le_antisymm h1 h2
          rw [h3]
          ring
        · by_cases hz2 : y₂ tstar u = 0
          · have h1 := hdomβ v hvR u huS
            have h2 := hnn v u
            rw [hz2] at h1 ⊢
            have h3 : y v u = 0 := le_antisymm h1 h2
            rw [h3]
            ring
          · field_simp
      · -- u ∈ S, v ∈ S : the kept side of instance 2
        have hstep : ∀ p ∈ L₁, ∀ q ∈ L₂,
            (if mg p.2 q.2 u = v then ν p q else 0)
            = if q.2 u = v then ν p q else 0 := by
          intro p hp q hq
          by_cases hub : u = q.2 tstar
          · rw [hub, hmgbP p hp q hq,
              if_neg (fun hh => (Finset.disjoint_left.mp hdisjRS)
                (hpair₁ p hp).1 (by rw [hh]; exact hvS)),
              if_neg (fun hh => htstarS
                (by rw [((hpair₂ q hq).2).symm.trans hh]; exact hvS))]
          · rw [hmgSP p hp q u huS hub]
        have hq2 : ∀ q ∈ L₂,
            (L₁.map (fun p => if q.2 u = v then ν p q else 0)).sum
            = if q.2 u = v then q.1 else 0 := by
          intro q hq
          by_cases h : q.2 u = v
          · rw [if_pos h, list_sum_congr _ _ (fun p => ν p q)
              (fun p hp => if_pos h)]
            exact hinner' q hq
          · rw [if_neg h]
            exact list_sum_zero_of_all _ _ (fun p hp => if_neg h)
        have hfin : (L₂.map (fun q => if q.2 u = v then q.1 else 0)).sum
            = y₂ u v := by
          rw [hL₂dec u v]
          exact list_sum_congr _ _ _ (fun q _ => by
            by_cases h : q.2 u = v
            · rw [if_pos h, if_pos ⟨h, Finset.mem_insert_of_mem huS⟩]
            · rw [if_neg h, if_neg (fun hh => h hh.1)])
        rw [list_sum_congr _ _ (fun p => (L₂.map (fun q =>
            if q.2 u = v then ν p q else 0)).sum) (fun p hp =>
          list_sum_congr _ _ _ (fun q hq => hstep p hp q hq)),
          list_double_swap L₁ L₂ (fun p q => if q.2 u = v then ν p q else 0),
          list_sum_congr _ _ _ hq2, hfin, hy₂ u v, if_pos huS, if_pos hvS]



/-! ### The perturbation step -/

lemma cut_add (B T : Finset (Fin n)) (f g : Fin n → Fin n → ℝ) (c : ℝ) :
    ∑ u ∈ T, ∑ v ∈ B, (f u v + c * g u v)
      = (∑ u ∈ T, ∑ v ∈ B, f u v) + c * (∑ u ∈ T, ∑ v ∈ B, g u v) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

lemma push_step (W : Finset (Fin n)) (hW : Even W.card)
    (y : Fin n → Fin n → ℝ) (hfeas : Feas W y)
    (hnotight : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card → 3 ≤ S.card →
      S.card + 3 ≤ W.card → 1 < ∑ u ∈ S, ∑ v ∈ W \ S, y u v)
    (z : Fin n → Fin n → ℝ) (hzne : z ≠ 0) (hzsym : ∀ u v, z u v = z v u)
    (hzdiag : ∀ v, z v v = 0) (hzsupp : ∀ u v, z u v ≠ 0 → y u v ≠ 0)
    (hzrow : ∀ v, ∑ u, z v u = 0) :
    ∃ ε : ℝ, 0 < ε ∧ Feas W (fun u v => y u v + ε * z u v) ∧
      ((∃ u v, y u v ≠ 0 ∧ y u v + ε * z u v = 0) ∨
        (∃ S : Finset (Fin n), S ⊆ W ∧ Odd S.card ∧ 3 ≤ S.card ∧
          S.card + 3 ≤ W.card ∧
          ∑ u ∈ S, ∑ v ∈ W \ S, (y u v + ε * z u v) = 1)) := by
  classical
  obtain ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ := hfeas
  have hzW : ∀ u v, z u v ≠ 0 → u ∈ W ∧ v ∈ W :=
    fun u v h => hsupp u v (hzsupp u v h)
  have hneg : ∃ u v, z u v < 0 := by
    by_contra hno
    push_neg at hno
    apply hzne
    funext u v
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x (_ : x ∈ Finset.univ) => hno v x)).mp (hzrow v) u (Finset.mem_univ u)
    rw [hzsym]
    exact h1
  -- trivial cuts of z vanish
  have hzc1 : ∀ v : Fin n, ∑ u ∈ ({v} : Finset (Fin n)),
      ∑ w ∈ W \ {v}, z u w = 0 := by
    intro v
    rw [Finset.sum_singleton]
    have h1 : ∑ w ∈ W \ {v}, z v w = ∑ w, z v w := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
      by_contra h0
      have hxW := (hzW v x h0).2
      have hxv : x ≠ v := fun h => h0 (by rw [h]; exact hzdiag v)
      exact hx (Finset.mem_sdiff.mpr
        ⟨hxW, fun h => hxv (Finset.mem_singleton.mp h)⟩)
    rw [h1]
    exact hzrow v
  have hzc1' : ∀ T : Finset (Fin n), T ⊆ W → T.card + 1 = W.card →
      ∑ u ∈ T, ∑ w ∈ W \ T, z u w = 0 := by
    intro T hTW hTcard
    have h1 : (W \ T).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hTW]
      have := Finset.card_le_card hTW
      omega
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp h1
    have h2 : ∀ u ∈ T, ∑ w ∈ W \ T, z u w = z u t := by
      intro u hu
      rw [ht, Finset.sum_singleton]
    rw [Finset.sum_congr rfl h2]
    have h3 : ∑ u ∈ T, z u t = ∑ u, z u t := by
      refine Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)
      by_contra h0
      by_cases hxt : x = t
      · rw [hxt] at h0
        exact h0 (hzdiag t)
      · have hxW := (hzW x t h0).1
        have : x ∈ W \ T := Finset.mem_sdiff.mpr ⟨hxW, hx⟩
        rw [ht, Finset.mem_singleton] at this
        exact hxt this
    rw [h3, Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hzsym u t)]
    exact hzrow t
  -- the stopping constraints
  set EC : Finset (Fin n × Fin n) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun e => z e.1 e.2 < 0) with hEC
  set SC : Finset (Finset (Fin n)) :=
    Finset.univ.powerset.filter (fun T => T ⊆ W ∧ Odd T.card ∧
      (∑ u ∈ T, ∑ w ∈ W \ T, z u w) < 0) with hSC
  have hSCsize : ∀ T ∈ SC, T ⊆ W ∧ Odd T.card ∧ 3 ≤ T.card
      ∧ T.card + 3 ≤ W.card ∧ (∑ u ∈ T, ∑ w ∈ W \ T, z u w) < 0 := by
    intro T hT
    rw [hSC] at hT
    obtain ⟨-, hTW, hTodd, hTz⟩ := Finset.mem_filter.mp hT
    have h1 : T.card ≠ 1 := by
      intro h
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h
      rw [hv, hzc1 v] at hTz
      norm_num at hTz
    have h2 : T.card + 1 ≠ W.card := by
      intro h
      rw [hzc1' T hTW h] at hTz
      norm_num at hTz
    have h3 : T.card ≤ W.card := Finset.card_le_card hTW
    obtain ⟨r, hr⟩ := hTodd
    obtain ⟨q, hq⟩ := hW
    exact ⟨hTW, ⟨r, hr⟩, by omega, by omega, hTz⟩
  set C : Finset ℝ := EC.image (fun e => y e.1 e.2 / (- z e.1 e.2))
    ∪ SC.image (fun T => ((∑ u ∈ T, ∑ w ∈ W \ T, y u w) - 1)
        / (- ∑ u ∈ T, ∑ w ∈ W \ T, z u w)) with hC
  have hCne : C.Nonempty := by
    obtain ⟨u, v, huv⟩ := hneg
    refine ⟨y u v / (- z u v), ?_⟩
    rw [hC]
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩)
    rw [hEC]
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_univ u, Finset.mem_univ v⟩, huv⟩
  have hCpos : ∀ c ∈ C, 0 < c := by
    intro c hc
    rw [hC] at hc
    rcases Finset.mem_union.mp hc with h | h
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h
      rw [hEC] at he
      have hze := (Finset.mem_filter.mp he).2
      have hye : y e.1 e.2 ≠ 0 := hzsupp e.1 e.2 (ne_of_lt hze)
      have hy0 := hnn e.1 e.2
      exact div_pos (lt_of_le_of_ne hy0 (Ne.symm hye)) (by linarith)
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hSCsize T hT
      have h6 := hnotight T h1 h2 h3 h4
      exact div_pos (by linarith) (by linarith)
  set ε := C.min' hCne with hεdef
  have hεmem : ε ∈ C := Finset.min'_mem C hCne
  have hεle : ∀ c ∈ C, ε ≤ c := fun c hc => Finset.min'_le C c hc
  have hεpos : 0 < ε := hCpos ε hεmem
  refine ⟨ε, hεpos, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u v
    show y u v + ε * z u v = y v u + ε * z v u
    rw [hsym, hzsym]
  · intro u v
    show 0 ≤ y u v + ε * z u v
    by_cases h : 0 ≤ z u v
    · have := hnn u v
      nlinarith
    · push_neg at h
      have hmem : y u v / (- z u v) ∈ C := by
        rw [hC]
        refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(u, v), ?_, rfl⟩)
        rw [hEC]
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ u, Finset.mem_univ v⟩, h⟩
      have h1 := hεle _ hmem
      rw [le_div_iff₀ (by linarith : (0:ℝ) < - z u v)] at h1
      linarith
  · intro v
    show y v v + ε * z v v = 0
    rw [hdiag, hzdiag]
    ring
  · intro u v h0
    have h1 : y u v ≠ 0 := by
      by_contra hy0
      apply h0
      show y u v + ε * z u v = 0
      have hz0 : z u v = 0 := by
        by_contra hz1
        exact (hzsupp u v hz1) hy0
      rw [hy0, hz0]
      ring
    exact hsupp u v h1
  · intro v hv
    show ∑ u, (y v u + ε * z v u) = 1
    rw [Finset.sum_add_distrib, hdeg v hv, ← Finset.mul_sum, hzrow v]
    ring
  · intro T hTW hTodd
    show 1 ≤ ∑ u ∈ T, ∑ w ∈ W \ T, (y u w + ε * z u w)
    rw [cut_add]
    by_cases h : 0 ≤ ∑ u ∈ T, ∑ w ∈ W \ T, z u w
    · have h1 := hodd T hTW hTodd
      nlinarith
    · push_neg at h
      have hmem : ((∑ u ∈ T, ∑ w ∈ W \ T, y u w) - 1)
          / (- ∑ u ∈ T, ∑ w ∈ W \ T, z u w) ∈ C := by
        rw [hC]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨T, ?_, rfl⟩)
        rw [hSC]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr (Finset.subset_univ T), hTW, hTodd, h⟩
      have h1 := hεle _ hmem
      rw [le_div_iff₀ (by linarith : (0:ℝ) < - ∑ u ∈ T, ∑ w ∈ W \ T, z u w)] at h1
      linarith
  · -- the binding constraint at the minimum
    rw [hC] at hεmem
    rcases Finset.mem_union.mp hεmem with h | h
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
      rw [hEC] at he
      have hze := (Finset.mem_filter.mp he).2
      have hye : y e.1 e.2 ≠ 0 := hzsupp e.1 e.2 (ne_of_lt hze)
      refine Or.inl ⟨e.1, e.2, hye, ?_⟩
      rw [← heq]
      have hz0 : z e.1 e.2 ≠ 0 := ne_of_lt hze
      field_simp
      ring
    · obtain ⟨T, hT, heq⟩ := Finset.mem_image.mp h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hSCsize T hT
      refine Or.inr ⟨T, h1, h2, h3, h4, ?_⟩
      rw [cut_add, ← heq]
      have hz0 : (∑ u ∈ T, ∑ w ∈ W \ T, z u w) ≠ 0 := ne_of_lt h5
      field_simp
      ring



/-! ### Convex combination of two decompositions -/

lemma decomp_combine (W : Finset (Fin n)) (y y₁ y₂ : Fin n → Fin n → ℝ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hyc : ∀ u v, y u v = θ * y₁ u v + (1 - θ) * y₂ u v)
    (L₁ L₂ : List (ℝ × (Fin n → Fin n)))
    (h₁ : IsDecomp W y₁ L₁) (h₂ : IsDecomp W y₂ L₂) :
    ∃ L, IsDecomp W y L := by
  obtain ⟨h₁ne, h₁mem, h₁sum, h₁dec⟩ := h₁
  obtain ⟨h₂ne, h₂mem, h₂sum, h₂dec⟩ := h₂
  have hscale : ∀ (L' : List (ℝ × (Fin n → Fin n))) (c : ℝ) (u v : Fin n),
      ((L'.map (fun p => (c * p.1, p.2))).map
        (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0)).sum
      = c * (L'.map (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0)).sum := by
    intro L' c u v
    rw [List.map_map]
    calc ((fun p : ℝ × (Fin n → Fin n) =>
            if p.2 u = v ∧ u ∈ W then p.1 else 0) ∘
            (fun p => (c * p.1, p.2)) |> L'.map).sum
        = (L'.map (fun p => c * (if p.2 u = v ∧ u ∈ W then p.1 else 0))).sum :=
          list_sum_congr _ _ _ (fun p _ => by
            show (if p.2 u = v ∧ u ∈ W then c * p.1 else 0)
              = c * (if p.2 u = v ∧ u ∈ W then p.1 else 0)
            by_cases h : p.2 u = v ∧ u ∈ W
            · rw [if_pos h, if_pos h]
            · rw [if_neg h, if_neg h]
              ring)
      _ = c * (L'.map (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0)).sum :=
          list_sum_scale _ _ _
  have hsumscale : ∀ (L' : List (ℝ × (Fin n → Fin n))) (c : ℝ),
      ((L'.map (fun p => (c * p.1, p.2))).map Prod.fst).sum
      = c * (L'.map Prod.fst).sum := by
    intro L' c
    rw [List.map_map]
    calc ((Prod.fst ∘ (fun p : ℝ × (Fin n → Fin n) => (c * p.1, p.2)))
          |> L'.map).sum
        = (L'.map (fun p => c * p.1)).sum :=
          list_sum_congr _ _ _ (fun p _ => rfl)
      _ = c * (L'.map Prod.fst).sum := list_sum_scale _ _ _
  refine ⟨L₁.map (fun p => (θ * p.1, p.2))
    ++ L₂.map (fun p => ((1 - θ) * p.1, p.2)), ?_, ?_, ?_, ?_⟩
  · intro h
    rw [List.append_eq_nil_iff] at h
    exact h₁ne (List.map_eq_nil_iff.mp h.1)
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp h
      exact ⟨mul_pos hθ0 (h₁mem p' hp').1, (h₁mem p' hp').2.1,
        (h₁mem p' hp').2.2⟩
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.mp h
      exact ⟨mul_pos (by linarith) (h₂mem p' hp').1, (h₂mem p' hp').2.1,
        (h₂mem p' hp').2.2⟩
  · rw [List.map_append, List.sum_append, hsumscale, hsumscale, h₁sum, h₂sum]
    ring
  · intro u v
    rw [hyc u v, h₁dec u v, h₂dec u v, List.map_append, List.sum_append,
      hscale, hscale]

/-! ### The main induction -/

lemma decomp_main : ∀ NW : ℕ, ∀ (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ),
    W.card ≤ NW → Even W.card → Feas W y → ∃ L, IsDecomp W y L := by
  intro NW
  induction NW with
  | zero =>
    intro W y hcard hW hfeas
    have hWempty : W = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hWempty
    exact ⟨_, decomp_empty y hfeas.2.2.2.1⟩
  | succ NW ihW =>
    suffices h : ∀ K : ℕ, ∀ (W : Finset (Fin n)) (y : Fin n → Fin n → ℝ),
        W.card ≤ NW + 1 → Even W.card → Feas W y →
        ((Finset.univ ×ˢ Finset.univ).filter
          (fun e : Fin n × Fin n => y e.1 e.2 ≠ 0)).card ≤ K →
        ∃ L, IsDecomp W y L by
      intro W y hcard hW hfeas
      exact h _ W y hcard hW hfeas (le_refl _)
    intro K
    induction K with
    | zero =>
      intro W y hcard hW hfeas hsupp0
      have hy0 : ∀ u v, y u v = 0 := by
        intro u v
        by_contra h0
        have hmem : (u, v) ∈ (Finset.univ ×ˢ Finset.univ).filter
            (fun e : Fin n × Fin n => y e.1 e.2 ≠ 0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_univ u, Finset.mem_univ v⟩, h0⟩
        have := Finset.card_pos.mpr ⟨_, hmem⟩
        omega
      have hWempty : W = ∅ := by
        by_contra hne
        obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hd := hfeas.2.2.2.2.1 v hv
        rw [Finset.sum_eq_zero (fun u _ => hy0 v u)] at hd
        norm_num at hd
      subst hWempty
      exact ⟨_, decomp_empty y hfeas.2.2.2.1⟩
    | succ K ihK =>
      intro W y hcard hW hfeas hsuppK
      obtain ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩ := id hfeas
      by_cases hWe : W = ∅
      · subst hWe
        exact ⟨_, decomp_empty y hsupp⟩
      by_cases hunit : ∃ a b, y a b = 1
      · obtain ⟨a, b, hab⟩ := hunit
        exact decomp_strip NW ihW W y (by omega) hW hfeas a b hab
      by_cases htight : ∃ S : Finset (Fin n), S ⊆ W ∧ Odd S.card ∧
          3 ≤ S.card ∧ S.card + 3 ≤ W.card ∧
          ∑ u ∈ S, ∑ v ∈ W \ S, y u v = 1
      · obtain ⟨S, h1, h2, h3, h4, h5⟩ := htight
        exact decomp_contract NW ihW W y (by omega) hW hfeas S h1 h2 h3 h4 h5
      -- neither: perturb along a balanced support direction
      have hnotight : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
          3 ≤ S.card → S.card + 3 ≤ W.card →
          1 < ∑ u ∈ S, ∑ v ∈ W \ S, y u v := by
        intro S hs1 hs2 hs3 hs4
        rcases lt_or_eq_of_le (hodd S hs1 hs2) with h | h
        · exact h
        · exact absurd ⟨S, hs1, hs2, hs3, hs4, h.symm⟩ htight
      have hfrac : ∀ u v, y u v ≠ 0 → y u v < 1 := by
        intro u v h0
        have huW := (hsupp u v h0).1
        have h1 : y u v ≤ 1 := by
          rw [← hdeg u huW]
          exact Finset.single_le_sum (fun x _ => hnn u x) (Finset.mem_univ v)
        rcases lt_or_eq_of_le h1 with h | h
        · exact h
        · exact absurd ⟨u, v, h⟩ hunit
      have hWn : W.Nonempty := Finset.nonempty_iff_ne_empty.mpr hWe
      obtain ⟨z, hzne, hzsym, hzdiag, hzsupp, hzrow⟩ :=
        support_perturbation n W hW hWn y hsym hnn hdiag hsupp hdeg hfrac
          (fun S h1 h2 => hodd S h1 h2)
      obtain ⟨z', hz'⟩ : ∃ f : Fin n → Fin n → ℝ, ∀ u v, f u v = - z u v :=
        ⟨_, fun _ _ => rfl⟩
      obtain ⟨ε₁, hε₁pos, hfeas₁, halt₁⟩ := push_step W hW y hfeas hnotight
        z hzne hzsym hzdiag hzsupp hzrow
      obtain ⟨ε₂, hε₂pos, hfeas₂, halt₂⟩ := push_step W hW y hfeas hnotight
        z' (fun h => hzne (funext (fun u => funext (fun v => by
          have h1 := congrFun (congrFun h u) v
          rw [hz' u v] at h1
          have h2 : - z u v = 0 := h1
          exact neg_eq_zero.mp h2))))
        (fun u v => by rw [hz' u v, hz' v u, hzsym])
        (fun v => by rw [hz' v v, hzdiag]; ring)
        (fun u v h => hzsupp u v (fun h0 => h (by rw [hz' u v, h0]; ring)))
        (fun v => by
          rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hz' v u),
            Finset.sum_neg_distrib, hzrow v]
          ring)
      -- decompose either endpoint
      have hend : ∀ (ε : ℝ) (w : Fin n → Fin n → ℝ),
          Feas W (fun u v => y u v + ε * w u v) →
          (∀ u v, w u v ≠ 0 → y u v ≠ 0) →
          ((∃ u v, y u v ≠ 0 ∧ y u v + ε * w u v = 0) ∨
            (∃ S : Finset (Fin n), S ⊆ W ∧ Odd S.card ∧ 3 ≤ S.card ∧
              S.card + 3 ≤ W.card ∧
              ∑ u ∈ S, ∑ v ∈ W \ S, (y u v + ε * w u v) = 1)) →
          ∃ L, IsDecomp W (fun u v => y u v + ε * w u v) L := by
        intro ε w hf' hwsupp halt
        rcases halt with ⟨u0, v0, hne0, hzero0⟩ | ⟨S, h1, h2, h3, h4, h5⟩
        · refine ihK W _ hcard hW hf' ?_
          have hsubset : (Finset.univ ×ˢ Finset.univ).filter
              (fun e : Fin n × Fin n => y e.1 e.2 + ε * w e.1 e.2 ≠ 0)
              ⊆ (Finset.univ ×ˢ Finset.univ).filter
              (fun e : Fin n × Fin n => y e.1 e.2 ≠ 0) := by
            intro e he
            obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
            refine Finset.mem_filter.mpr ⟨he1, ?_⟩
            intro h0
            apply he2
            have hw : w e.1 e.2 = 0 := by
              by_contra hw0
              exact (hwsupp e.1 e.2 hw0) h0
            rw [h0, hw]
            ring
          have hsub := (Finset.ssubset_iff_of_subset hsubset).mpr
            ⟨(u0, v0), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_univ u0, Finset.mem_univ v0⟩, hne0⟩,
              fun hmem => (Finset.mem_filter.mp hmem).2 hzero0⟩
          have := Finset.card_lt_card hsub
          omega
        · exact decomp_contract NW ihW W _ (by omega) hW hf' S h1 h2 h3 h4 h5
      obtain ⟨L₁, hL₁⟩ := hend ε₁ z hfeas₁ hzsupp halt₁
      obtain ⟨L₂, hL₂⟩ := hend ε₂ z' hfeas₂
        (fun u v h => hzsupp u v (fun h0 => h (by rw [hz' u v, h0]; ring)))
        halt₂
      refine decomp_combine W y _ _ (ε₂ / (ε₁ + ε₂)) ?_ ?_ ?_ L₁ L₂ hL₁ hL₂
      · exact div_pos hε₂pos (by linarith)
      · rw [div_lt_one (by linarith)]
        linarith
      · intro u v
        rw [hz' u v]
        field_simp
        ring

end MetricTSP

open MetricTSP

theorem solution (n : ℕ) (W : Finset (Fin n)) (hW : Even W.card)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hodd : ∀ S : Finset (Fin n), S ⊆ W → Odd S.card →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ L : List (ℝ × (Fin n → Fin n)), L ≠ [] ∧
      (∀ p ∈ L, 0 < p.1 ∧
        (∀ v ∈ W, p.2 v ∈ W ∧ p.2 (p.2 v) = v ∧ p.2 v ≠ v) ∧
        (∀ v ∉ W, p.2 v = v)) ∧
      (L.map Prod.fst).sum = 1 ∧
      (∀ u v, y u v
        = (L.map (fun p => if p.2 u = v ∧ u ∈ W then p.1 else 0)).sum) := by
  obtain ⟨L, h1, h2, h3, h4⟩ := MetricTSP.decomp_main W.card W y (le_refl _)
    hW ⟨hsym, hnn, hdiag, hsupp, hdeg, hodd⟩
  exact ⟨L, h1, h2, h3, h4⟩
