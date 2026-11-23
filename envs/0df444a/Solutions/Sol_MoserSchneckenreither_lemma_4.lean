-- Prove2me | solution 1 for MoserSchneckenreither.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T05:07:59.728832+00:00
-- url     : https://prove2.me/submissions/19a67c90-df84-4f6e-a3a2-22955932d1f3

import Definitions.Def_MoserSchneckenreither_Typing
import Mathlib.Algebra.Order.Ring.NNRat

namespace MSLemma4
open MoserSchneckenreither

variable {sig : Signature} {P : Problem sig}

theorem subst_subst (σ τ : ℕ → Term sig) (t : Term sig) :
    (t.subst τ).subst σ = t.subst (fun x ↦ (τ x).subst σ) := by
  induction t with
  | var x => rfl
  | app f ts ih => simp only [Term.subst, ih]

theorem mem_vars_subst (τ : ℕ → Term sig) (t : Term sig) (x : ℕ) :
    x ∈ (t.subst τ).vars → ∃ y ∈ t.vars, x ∈ (τ y).vars := by
  induction t with
  | var y => intro h; exact ⟨y, by simp [Term.vars], h⟩
  | app f ts ih =>
    intro h
    simp only [Term.subst, Term.vars, List.mem_flatten, List.mem_ofFn] at h
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := h
    obtain ⟨y, hy, hxy⟩ := ih i hi
    refine ⟨y, ?_, hxy⟩
    simp only [Term.vars, List.mem_flatten, List.mem_ofFn]
    exact ⟨_, ⟨i, rfl⟩, hy⟩

theorem vars_sub (F : AnnotatedSignature P) {m : Mode} {Γ : Context} {k : ℚ≥0} {t : Term sig}
    {q : Annotation} (h : Typing F m Γ k t q) : ∀ x ∈ t.vars, x ∈ Γ.keys := by
  induction h with
  | app mode f a ha xs hx =>
    intro x hx'
    simp only [Term.vars, List.mem_flatten, List.mem_ofFn] at hx'
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx'
    simp only [List.mem_singleton] at hi
    subst hi
    simp only [Context.keys, flatContext, List.map_ofFn, List.mem_ofFn]
    exact ⟨i, rfl⟩
  | var mode x q => intro y hy; simpa [Term.vars, Context.keys] using hy
  | comp f ts xs ps Γs ks k₀ q hx hfresh hdisjoint hlinear hhead hargs ihhead ihargs =>
    intro x hx'
    simp only [Term.vars, List.mem_flatten, List.mem_ofFn] at hx'
    obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx'
    have := ihargs i x hi
    simp only [Context.keys, List.mem_map] at this ⊢
    obtain ⟨a, ha, rfl⟩ := this
    exact ⟨a, List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, ha⟩, rfl⟩
  | share Γ x y z p₁ p₂ p q t k hshare hxy hxz hyz hx hy hz h ih =>
    intro w hw
    unfold Term.rename at hw
    obtain ⟨v, hv, hwv⟩ := mem_vars_subst _ t w hw
    simp only [Term.vars, List.mem_singleton] at hwv
    subst hwv
    have := ih v hv
    simp only [Context.keys, List.map_append, List.mem_append, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    by_cases hv' : v = x ∨ v = y
    · simp [hv']
    · simp only [hv', if_false]
      rcases this with h1 | h1 | h1
      · exact Or.inl h1
      · exact absurd (Or.inl h1) hv'
      · exact absurd (Or.inr h1) hv'
  | perm hperm h ih =>
    intro x hx
    exact ((hperm.map Prod.fst).mem_iff).1 (ih x hx)
  | w1 h hk ih => exact ih
  | w2 Γ x p r q k t h hr ih =>
    intro w hw
    have := ih w hw
    simpa [Context.keys] using this
  | w3 h hq ih => exact ih
  | w4 Γ x p q k t hx h ih =>
    intro w hw
    have := ih w hw
    simp only [Context.keys, List.map_append, List.mem_append] at this ⊢
    exact Or.inl this

theorem ground_subst (σ : Substitution sig) (hn : σ.Normalised P) (t : Term sig)
    (hv : ∀ x ∈ t.vars, x ∈ σ.domain) : (t.subst σ.apply).vars = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_vars_subst _ t x hx
  have hd := hv y hy
  simp only [Substitution.apply, if_pos hd] at hxy
  rw [(hn y hd).1] at hxy
  simp at hxy

theorem cons_dom (F : AnnotatedSignature P) {σ : Substitution sig} {Γ : Context}
    (hc : Consistent F σ Γ) : ∀ x ∈ Γ.keys, x ∈ σ.domain := by
  intro x hx
  simp only [Context.keys, List.mem_map] at hx
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
  exact (hc.2 a b hab).1

theorem cons_sublist (F : AnnotatedSignature P) {σ : Substitution sig} {Γ Δ : Context}
    (hc : Consistent F σ Γ) (hs : Δ.Sublist Γ) : Consistent F σ Δ :=
  ⟨List.Nodup.sublist (hs.map _) hc.1, fun x q hx ↦ hc.2 x q (hs.subset hx)⟩

theorem linear_of_nil (t : Term sig) (h : t.vars = []) : t.Linear := by
  unfold Term.Linear; rw [h]; exact List.nodup_nil

theorem flatten_nil (n : ℕ) : (List.ofFn fun _ : Fin n ↦ ([] : Context)).flatten = [] := by
  simp

theorem main (F : AnnotatedSignature P) {m : Mode} {Γ : Context} {k : ℚ≥0} {t : Term sig}
    {q : Annotation} (h : Typing F m Γ k t q) :
    m = .full → ∀ σ : Substitution sig, σ.Normalised P → Consistent F σ Γ →
      ∃ k', Typing F .full [] k' (t.subst σ.apply) q := by
  induction h with
  | app mode f a ha xs hx =>
    intro hm σ hn hc
    have hT := Typing.app (F := F) mode f a ha xs hx
    have hg := ground_subst σ hn _ (fun x hx' ↦ cons_dom F hc x (vars_sub F hT x hx'))
    have hin : ∀ i, (xs i, a.inputs i) ∈ flatContext xs a.inputs := fun i ↦
      List.mem_ofFn.2 ⟨i, rfl⟩
    have hks : ∀ i, ∃ k, Typing F .full [] k (σ.apply (xs i)) (a.inputs i) :=
      fun i ↦ (hc.2 _ _ (hin i)).2
    choose ks hks using hks
    have hinj : Function.Injective (fun i : Fin (sig.arity f) ↦ i.val) := Fin.val_injective
    have hC := Typing.comp (F := F) (mode := .full) f (fun i ↦ σ.apply (xs i)) (fun i ↦ i.val)
      a.inputs (fun _ ↦ []) ks a.cost a.output hinj (by simp [Context.keys])
      (by simp [Context.keys]) (linear_of_nil _ hg)
      (Typing.app .full f a ha _ hinj) hks
    rw [flatten_nil] at hC
    exact ⟨_, hC⟩
  | var mode x q =>
    intro hm σ hn hc
    exact (hc.2 x q (by simp)).2
  | comp f ts xs ps Γs ks k₀ q hx hfresh hdisjoint hlinear hhead hargs ihhead ihargs =>
    intro hm σ hn hc
    have hT := Typing.comp f ts xs ps Γs ks k₀ q hx hfresh hdisjoint hlinear hhead hargs
    have hg := ground_subst σ hn _ (fun x hx' ↦ cons_dom F hc x (vars_sub F hT x hx'))
    have hks : ∀ i, ∃ k, Typing F .full [] k ((ts i).subst σ.apply) (ps i) := fun i ↦
      ihargs i hm σ hn (cons_sublist F hc
        (List.sublist_flatten_of_mem (List.mem_ofFn.2 ⟨i, rfl⟩)))
    choose ks' hks' using hks
    subst hm
    have hC := Typing.comp (F := F) (mode := .full) f (fun i ↦ (ts i).subst σ.apply) xs ps
      (fun _ ↦ []) ks' k₀ q hx (by simp [Context.keys]) (by simp [Context.keys])
      (linear_of_nil _ hg) hhead hks'
    rw [flatten_nil] at hC
    exact ⟨_, hC⟩
  | share Γ x y z p₁ p₂ p q t k hshare hxy hxz hyz hx hy hz h ih =>
    intro hm σ hn hc
    have hzd : z ∈ σ.domain := (hc.2 z p (by simp)).1
    let σ' : Substitution sig := ⟨σ.domain ∪ {x, y},
      fun w ↦ if w = x ∨ w = y then σ.assignment z else σ.assignment w⟩
    have happ : ∀ w, σ'.apply w = σ.apply (if w = x ∨ w = y then z else w) := by
      intro w
      by_cases hw : w = x ∨ w = y
      · have hw' : w ∈ σ.domain ∪ {x, y} := by
          rcases hw with rfl | rfl <;> simp
        simp only [Substitution.apply, σ', hw, if_true, hw', if_pos hzd]
      · have hiff : w ∈ σ.domain ∪ {x, y} ↔ w ∈ σ.domain := by
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          tauto
        simp only [Substitution.apply, σ', hw, if_false, hiff]
    have hn' : σ'.Normalised P := by
      intro w hw
      by_cases hw' : w = x ∨ w = y
      · simp only [σ', hw', if_true]; exact hn z hzd
      · have : w ∈ σ.domain := by
          simp only [σ', Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
          tauto
        simp only [σ', hw', if_false]; exact hn w this
    have hΓv : Γ.keys.Nodup := by
      have := hc.1
      simp only [Context.Valid, Context.keys, List.map_append] at this
      exact this.sublist (List.sublist_append_left _ _)
    have hc' : Consistent F σ' (Γ ++ [(x, p₁), (y, p₂)]) := by
      refine ⟨?_, ?_⟩
      · simp only [Context.Valid, Context.keys, List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨hΓv, by simp [hxy], ?_⟩
        intro a ha b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · exact fun e ↦ hx (e ▸ ha)
        · exact fun e ↦ hy (e ▸ ha)
      · intro w s hw
        rcases List.mem_append.1 hw with hw | hw
        · have hk : w ∈ Γ.keys := List.mem_map.2 ⟨(w, s), hw, rfl⟩
          have h1 : w ≠ x := fun e ↦ hx (e ▸ hk)
          have h2 : w ≠ y := fun e ↦ hy (e ▸ hk)
          obtain ⟨hd, k', hk'⟩ := hc.2 w s (List.mem_append_left _ hw)
          refine ⟨by simp [σ', hd], k', ?_⟩
          rw [happ]; simpa [h1, h2] using hk'
        · obtain ⟨hd, k', hk'⟩ := hc.2 z p (by simp)
          simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hw
          rcases hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · refine ⟨by simp [σ'], k', ?_⟩
            rw [happ]; simp only [true_or, if_true]
            exact Typing.w3 hk' (by rw [← hshare]; exact le_self_add)
          · refine ⟨by simp [σ'], k', ?_⟩
            rw [happ]; simp only [or_true, if_true]
            exact Typing.w3 hk' (by rw [← hshare]; exact le_add_self)
    obtain ⟨k', hk'⟩ := ih hm σ' hn' hc'
    refine ⟨k', ?_⟩
    have heq : (t.rename fun w ↦ if w = x ∨ w = y then z else w).subst σ.apply =
        t.subst σ'.apply := by
      unfold Term.rename; rw [subst_subst]
      congr 1; funext w; rw [happ]; rfl
    rw [heq]; exact hk'
  | perm hperm h ih =>
    intro hm σ hn hc
    refine ih hm σ hn ⟨?_, fun x q hx ↦ hc.2 x q (hperm.mem_iff.1 hx)⟩
    exact ((hperm.map Prod.fst).nodup_iff).2 hc.1
  | w1 h hk ih => intro _ σ hn hc; exact ih rfl σ hn hc
  | w2 Γ x p r q k t h hr ih =>
    intro _ σ hn hc
    refine ih rfl σ hn ⟨?_, ?_⟩
    · have := hc.1
      simpa [Context.Valid, Context.keys] using this
    · intro w s hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hc.2 w s (List.mem_append_left _ hw)
      · simp only [List.mem_singleton, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        obtain ⟨hd, k', hk'⟩ := hc.2 w p (by simp)
        exact ⟨hd, k', Typing.w3 hk' hr⟩
  | w3 h hq ih =>
    intro _ σ hn hc
    obtain ⟨k', hk'⟩ := ih rfl σ hn hc
    exact ⟨k', Typing.w3 hk' hq⟩
  | w4 Γ x p q k t hx h ih =>
    intro _ σ hn hc
    exact ih rfl σ hn (cons_sublist F hc (List.sublist_append_left _ _))

end MSLemma4

open MoserSchneckenreither in
theorem solution {sig : Signature} {P : Problem sig} (F : AnnotatedSignature P)
    (Γ : Context) (σ : Substitution sig) (hn : σ.Normalised P) (hc : Consistent F σ Γ)
    (t : Term sig) (q : Annotation) (k : ℚ≥0) (ht : Typing F .full Γ k t q) :
    ∃ k' : ℚ≥0, Typing F .full [] k' (t.subst σ.apply) q :=
  MSLemma4.main F ht rfl σ hn hc
