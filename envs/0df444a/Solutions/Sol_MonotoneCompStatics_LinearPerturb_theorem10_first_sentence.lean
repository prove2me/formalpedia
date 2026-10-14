-- Prove2me | solution 1 for MonotoneCompStatics.LinearPerturb.theorem10_first_sentence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:27:41.272987+00:00
-- url     : https://prove2.me/submissions/42d41f65-bb04-4e2b-9ab5-14364e20ae5e

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_SingleCrossing



namespace MonotoneCompStatics.LinearPerturb

lemma dot_modular {n : ℕ} (p a b : Fin n → ℝ) :
    p ⬝ᵥ (a ⊔ b) + p ⬝ᵥ (a ⊓ b) = p ⬝ᵥ a + p ⬝ᵥ b := by
  simp only [dotProduct]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sup_apply, Pi.inf_apply]
  rcases le_total (a i) (b i) with h | h
  · simp [h] <;> ring
  · simp [h] <;> ring

lemma key_core {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ)
    (hq : ∀ p : Fin n → ℝ, ∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn
        (fun x => f x t + p ⬝ᵥ x) Set.univ)
    (hs : ∀ p : Fin n → ℝ, MonotoneCompStatics.Monotonicity.SingleCrossing
        (fun x t => f x t + p ⬝ᵥ x))
    (a b : Fin n → ℝ) (t1 t2 : ℝ) (h : t1 ≤ t2) :
    f a t1 + f b t2 ≤ f (a ⊔ b) t2 + f (a ⊓ b) t1 := by
  by_cases hab : a ≤ b
  · rw [sup_eq_right.2 hab, inf_eq_left.2 hab]; linarith
  · have : ∃ i, b i < a i := by
      by_contra hc
      push Not at hc
      exact hab hc
    obtain ⟨i, hi⟩ := this
    have hinf : (a ⊓ b) i = b i := by simp [le_of_lt hi]
    set c : ℝ := (f (a ⊓ b) t1 - f a t1) / (a i - b i) with hc
    have hpos : a i - b i ≠ 0 := by linarith
    have hcc : c * (a i - b i) = f (a ⊓ b) t1 - f a t1 := by
      rw [hc]; field_simp
    let p : Fin n → ℝ := Pi.single i c
    have hp : ∀ x : Fin n → ℝ, p ⬝ᵥ x = c * x i := by
      intro x
      simp [p, dotProduct, Pi.single_apply]
    have hmod := dot_modular p a b
    rw [hp, hp, hp, hp] at hmod
    have heq : f (a ⊓ b) t1 + p ⬝ᵥ (a ⊓ b) = f a t1 + p ⬝ᵥ a := by
      rw [hp, hp, hinf]; nlinarith
    have hq1 := (hq p t1 (Set.mem_univ a) (Set.mem_univ b)).1 (by simp only; linarith)
    simp only at hq1
    have hfin : f b t2 + p ⬝ᵥ b ≤ f (a ⊔ b) t2 + p ⬝ᵥ (a ⊔ b) := by
      rcases h.lt_or_eq with hlt | heq2
      · have hlt' : b < a ⊔ b := by
          refine lt_of_le_of_ne le_sup_right ?_
          intro he
          exact hab (by rw [← sup_eq_right]; exact he.symm)
        exact (hs p hlt' hlt).2 hq1
      · subst heq2; exact hq1
    rw [hp, hp] at hfin
    have : (a ⊔ b) i = a i := by simp [le_of_lt hi]
    rw [this] at hfin
    rw [hinf] at *
    nlinarith

theorem t10_core {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    (∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ := by
  constructor
  · intro h
    rintro ⟨a, t1⟩ _ ⟨b, t2⟩ _
    have hq := fun p => (h p).1
    have hs := fun p => (h p).2
    simp only [Prod.mk_sup_mk, Prod.mk_inf_mk]
    rcases le_total t1 t2 with h12 | h12
    · rw [sup_eq_right.2 h12, inf_eq_left.2 h12]
      exact key_core f hq hs a b t1 t2 h12
    · rw [sup_eq_left.2 h12, inf_eq_right.2 h12]
      have := key_core f hq hs b a t2 t1 h12
      rw [sup_comm, inf_comm]
      linarith
  · intro hf p
    have hmod := dot_modular p
    have hgsm : Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2 + p ⬝ᵥ z.1) Set.univ := by
      rintro ⟨a, t1⟩ _ ⟨b, t2⟩ _
      have := hf (Set.mem_univ (a, t1)) (Set.mem_univ (b, t2))
      have hm := hmod a b
      simp only [Prod.mk_sup_mk, Prod.mk_inf_mk] at this ⊢
      linarith
    refine ⟨fun t => ?_, ?_⟩
    · intro x _ y _
      have := hgsm (Set.mem_univ (x, t)) (Set.mem_univ (y, t))
      simp only [Prod.mk_sup_mk, Prod.mk_inf_mk, sup_idem, inf_idem] at this ⊢
      constructor <;> intro h1 <;> linarith
    · intro x' x'' hx t' t'' ht
      have := hgsm (Set.mem_univ (x', t'')) (Set.mem_univ (x'', t'))
      simp only [Prod.mk_sup_mk, Prod.mk_inf_mk] at this
      rw [sup_eq_left.2 hx.le, sup_eq_right.2 ht.le, inf_eq_right.2 hx.le,
        inf_eq_left.2 ht.le] at this
      simp only
      constructor <;> intro h1 <;> linarith

end MonotoneCompStatics.LinearPerturb

open MonotoneCompStatics.LinearPerturb


theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ → ℝ) :
    (∀ p : Fin n → ℝ, (∀ t, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => f x t + p ⬝ᵥ x) Set.univ) ∧
        MonotoneCompStatics.Monotonicity.SingleCrossing (fun x t => f x t + p ⬝ᵥ x)) ↔
      Supermodularity.Monotonicity.SupermodularOn
        (fun z : (Fin n → ℝ) × ℝ => f z.1 z.2) Set.univ := by
  exact t10_core f
