-- Prove2me | solution 1 for LasserreFC.FinConv.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:29:40.952663+00:00
-- url     : https://prove2.me/submissions/ed88acca-5003-4200-956d-73b4d74036a4

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy

open MvPolynomial LasserreFC.FinConv

/-- A sum of squares evaluates to a nonnegative number. -/
private lemma sos_eval_nonneg {n : ℕ} (u : Fin n → ℝ) (s : MvPolynomial (Fin n) ℝ)
    (hs : IsSumSq s) : 0 ≤ eval u s := by
  induction hs with
  | zero => simp
  | sq_add a hs ih =>
    rw [map_add, map_mul]
    nlinarith [mul_self_nonneg (eval u a)]

/-- A sum of squares vanishing at `u` has vanishing gradient at `u`. -/
private lemma sos_pderiv_eval {n : ℕ} (u : Fin n → ℝ) (s : MvPolynomial (Fin n) ℝ)
    (hs : IsSumSq s) (h0 : eval u s = 0) (k : Fin n) : eval u (pderiv k s) = 0 := by
  induction hs with
  | zero => simp
  | @sq_add a s hs ih =>
    rw [map_add, map_mul] at h0
    have h1 := sos_eval_nonneg u _ hs
    have ha : eval u a = 0 := by nlinarith [mul_self_nonneg (eval u a)]
    have hs0 : eval u s = 0 := by nlinarith [mul_self_nonneg (eval u a)]
    rw [map_add, pderiv_mul, map_add, map_add, map_mul, map_mul, ha, ih hs0]
    ring

theorem solution {n m1 m2 : ℕ} (P : POP n m1 m2)
    (hatt : ∀ k : ℕ, lasserreValue P k ≠ ⊥ → lasserreValue P k ≠ ⊤ →
      ∃ γ : ℝ, (γ : EReal) = lasserreValue P k ∧ P.f - C γ ∈ trunc P k)
    (fmin : ℝ) (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin)
    (u : Fin n → ℝ) (hu : u ∈ P.K) (hmin : IsMinOn (fun x => eval x P.f) P.K u)
    (hfooc : ¬ ∃ (lam : Fin m1 → ℝ) (mu : Fin m2 → ℝ),
      grad P.f u = ∑ i, lam i • grad (P.h i) u + ∑ j, mu j • grad (P.g j) u) :
    ∀ k : ℕ, lasserreValue P k ≠ (fmin : EReal) := by
  intro k hk
  obtain ⟨γ, hγ, hmem⟩ := hatt k (by rw [hk]; exact EReal.coe_ne_bot _)
    (by rw [hk]; exact EReal.coe_ne_top _)
  have hγf : γ = fmin := by exact_mod_cast hγ.trans hk
  subst hγf
  obtain ⟨a, ⟨φ, rfl, -⟩, b, ⟨σ0, σ, hσ0, -, hσj, rfl⟩, heq⟩ := hmem
  obtain ⟨huh, hug⟩ := hu
  -- f(u) = f_min
  have hfu : eval u P.f = γ := by
    obtain ⟨⟨x0, hx0, hx0f⟩, hlow⟩ := hfmin
    have h1 : eval u P.f ≤ eval x0 P.f := hmin hx0
    have h2 : γ ≤ eval u P.f := hlow ⟨u, ⟨huh, hug⟩, rfl⟩
    simp only at hx0f
    linarith
  -- evaluate the certificate at u
  have hev := congrArg (eval u) heq
  simp only [map_sub, map_add, map_sum, map_mul, eval_C, hfu, sub_self, huh, mul_zero,
    Finset.sum_const_zero, zero_add] at hev
  have hσ0n := sos_eval_nonneg u σ0 hσ0
  have hjn : ∀ j ∈ Finset.univ, 0 ≤ eval u (σ j) * eval u (P.g j) := fun j _ =>
    mul_nonneg (sos_eval_nonneg u _ (hσj j).1) (hug j)
  have hsumn := Finset.sum_nonneg hjn
  have hσ0z : eval u σ0 = 0 := by linarith
  have hsumz : ∑ j, eval u (σ j) * eval u (P.g j) = 0 := by linarith
  have hjz := (Finset.sum_eq_zero_iff_of_nonneg hjn).1 hsumz
  apply hfooc
  refine ⟨fun i => eval u (φ i), fun j => eval u (σ j), ?_⟩
  funext k
  have hd := congrArg (fun p => eval u (pderiv k p)) heq
  simp only [map_sub, pderiv_C, sub_zero, map_add, map_sum, pderiv_mul, map_mul, huh,
    mul_zero, zero_add] at hd
  rw [sos_pderiv_eval u σ0 hσ0 hσ0z k, zero_add] at hd
  simp only [grad, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hd]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  -- the term g_j(u) ∇σ_j(u) vanishes
  have : eval u (pderiv k (σ j)) * eval u (P.g j) = 0 := by
    rcases (hug j).eq_or_lt with h | h
    · rw [← h, mul_zero]
    · have hz : eval u (σ j) = 0 := by
        rcases mul_eq_zero.1 (hjz j (Finset.mem_univ j)) with h' | h'
        · exact h'
        · exact absurd h' h.ne'
      rw [sos_pderiv_eval u _ (hσj j).1 hz k, zero_mul]
  linarith
