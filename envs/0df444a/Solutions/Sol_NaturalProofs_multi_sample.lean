-- Prove2me | solution 1 for NaturalProofs.multi_sample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:39:38.484197+00:00
-- url     : https://prove2.me/submissions/ab9f0c07-6bbb-4f35-acd1-07e4e0a6a9db

module
public import Mathlib
public import Definitions.Def_NaturalProofs_Prob
public import Theorems.Thm_NaturalProofs_prob_equiv
public import Theorems.Thm_NaturalProofs_prob_fst
public import Theorems.Thm_NaturalProofs_prob_snd
public import Theorems.Thm_NaturalProofs_telescope
public import Theorems.Thm_NaturalProofs_exists_abs_ge_avg
public import Theorems.Thm_NaturalProofs_sum_resample

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]
namespace NaturalProofs
theorem _root_.solution [DecidableEq I] [Nonempty I] [Nonempty A] [Nonempty B] (g : A → B)
    (F : (I → B) → Bool) :
    ∃ (e : I) (c : I → B),
      |prob (fun L : I → A => F (fun i => g (L i))) - prob F| / Fintype.card I ≤
        |prob (fun u : A => F (Function.update c e (g u))) -
          prob (fun y : B => F (Function.update c e y))| := by
  set σ := Fintype.equivFin I
  set N := Fintype.card I
  let hyb : ℕ → (I → A × B) → I → B :=
    fun t ω i => if (σ i : ℕ) < t then (ω i).2 else g (ω i).1
  let q : ℕ → ℝ := fun t => prob (fun ω => F (hyb t ω))
  let ψ := Equiv.arrowProdEquivProdArrow I (fun _ => A) (fun _ => B)
  have hq0 : q 0 = prob (fun L : I → A => F (fun i => g (L i))) := by
    have : (fun ω => F (hyb 0 ω)) =
        fun ω => (fun p : (I → A) × (I → B) => F (fun i => g (p.1 i))) (ψ ω) := by
      funext ω
      simp [hyb, ψ]
    simp only [q]
    rw [this, prob_equiv ψ (fun p : (I → A) × (I → B) => F (fun i => g (p.1 i))),
      prob_fst (fun L : I → A => F (fun i => g (L i)))]
  have hqN : q N = prob F := by
    have : (fun ω => F (hyb N ω)) =
        fun ω => (fun p : (I → A) × (I → B) => F p.2) (ψ ω) := by
      funext ω
      simp only [hyb, ψ, Equiv.arrowProdEquivProdArrow_apply]
      congr 1
      funext i
      simp [(σ i).isLt]
    simp only [q]
    rw [this, prob_equiv ψ (fun p : (I → A) × (I → B) => F p.2), prob_snd F]
  obtain ⟨t, ht, hstep⟩ := telescope q N Fintype.card_pos
  set e := σ.symm ⟨t, ht⟩
  have hσe : (σ e : ℕ) = t := by simp [e]
  let P1 : (I → B) → ℝ := fun c => prob (fun u : A => F (Function.update c e (g u)))
  let P2 : (I → B) → ℝ := fun c => prob (fun y : B => F (Function.update c e y))
  have hupd1 : ∀ ω (z : A × B), hyb t (Function.update ω e z) =
      Function.update (hyb t ω) e (g z.1) := by
    intro ω z
    funext i
    by_cases hi : i = e
    · subst hi
      simp [hyb, hσe]
    · simp [hyb, Function.update_of_ne hi]
  have hupd2 : ∀ ω (z : A × B), hyb (t + 1) (Function.update ω e z) =
      Function.update (hyb t ω) e z.2 := by
    intro ω z
    funext i
    by_cases hi : i = e
    · subst hi
      simp [hyb, hσe]
    · have hne : (σ i : ℕ) ≠ t := by
        intro h'
        apply hi
        apply σ.injective
        exact Fin.ext (h'.trans hσe.symm)
      have : ((σ i : ℕ) < t + 1) ↔ ((σ i : ℕ) < t) := by omega
      simp [hyb, Function.update_of_ne hi, this]
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hinner : ∀ ω : I → A × B,
      ∑ z : A × B, (ind (F (hyb t (Function.update ω e z))) -
        ind (F (hyb (t + 1) (Function.update ω e z)))) =
      Fintype.card A * Fintype.card B * (P1 (hyb t ω) - P2 (hyb t ω)) := by
    intro ω
    simp only [hupd1, hupd2, Fintype.sum_prod_type, Finset.sum_sub_distrib, P1, P2, prob]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp
  have hdiff : q t - q (t + 1) =
      (∑ ω : I → A × B, (P1 (hyb t ω) - P2 (hyb t ω))) / Fintype.card (I → A × B) := by
    have hres := sum_resample e (fun ω : I → A × B =>
      ind (F (hyb t ω)) - ind (F (hyb (t + 1) ω)))
    simp only [hinner, Fintype.card_prod] at hres
    rw [← Finset.mul_sum, Nat.cast_mul] at hres
    have hsum : ∑ ω, (P1 (hyb t ω) - P2 (hyb t ω)) =
        ∑ ω : I → A × B, (ind (F (hyb t ω)) - ind (F (hyb (t + 1) ω))) := by
      have hAB : (Fintype.card A : ℝ) * Fintype.card B ≠ 0 := mul_ne_zero hA hB
      exact mul_left_cancel₀ hAB hres
    simp only [q, prob]
    rw [hsum, Finset.sum_sub_distrib, sub_div]
  obtain ⟨ω, hω⟩ := exists_abs_ge_avg (fun ω : I → A × B => P1 (hyb t ω) - P2 (hyb t ω))
  refine ⟨e, hyb t ω, ?_⟩
  have hc : (0 : ℝ) < Fintype.card (I → A × B) := by exact_mod_cast Fintype.card_pos
  rw [hq0, hqN] at hstep
  calc _ ≤ |q t - q (t + 1)| := hstep
    _ = |∑ ω : I → A × B, (P1 (hyb t ω) - P2 (hyb t ω))| / Fintype.card (I → A × B) := by
        rw [hdiff, abs_div, abs_of_pos hc]
    _ ≤ _ := hω
end NaturalProofs
