-- Prove2me | solution 1 for MarkovMixing.glauber_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:59:06.014101+00:00
-- url     : https://prove2.me/submissions/86f68fb9-78d5-4307-aaf4-8d7f9e344a4d

import Definitions.Def_mm_mcmc
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MarkovMixing

theorem solution {Vv S : Type*} [Fintype Vv] [DecidableEq Vv]
    [Fintype S] [DecidableEq S] [Nonempty Vv]
    (π : (Vv → S) → ℝ) (hπ : IsDist π) :
    (∀ x y : Vv → S, 0 ≤ glauber π x y) ∧
    (∀ x : Vv → S, 0 < π x → ∑ y, glauber π x y = 1) ∧
    DetailedBalance (glauber π) π ∧
    IsStationary (glauber π) π := by
  classical
  set C : Vv → S → Prop := fun _ _ => True with hC
  -- the conditioning set at a vertex, and its mass
  set nb : (Vv → S) → Vv → Finset (Vv → S) :=
    fun x v => Finset.univ.filter (fun z : Vv → S => ∀ w : Vv, w ≠ v → z w = x w) with hnb
  set D : (Vv → S) → Vv → ℝ := fun x v => ∑ z ∈ nb x v, π z with hD
  have hglauber : ∀ x y : Vv → S,
      glauber π x y = (Fintype.card Vv : ℝ)⁻¹ *
        ∑ v : Vv, (if ∀ w : Vv, w ≠ v → y w = x w then π y / D x v else 0) := by
    intro x y
    rfl
  have hDnonneg : ∀ (x : Vv → S) (v : Vv), 0 ≤ D x v :=
    fun x v => Finset.sum_nonneg fun z _ => hπ.1 z
  have hcardpos : (0:ℝ) < (Fintype.card Vv : ℝ) := by exact_mod_cast Fintype.card_pos
  -- membership facts
  have hmem : ∀ (x z : Vv → S) (v : Vv),
      z ∈ nb x v ↔ ∀ w : Vv, w ≠ v → z w = x w := by
    intro x z v
    rw [hnb, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ z, h⟩⟩
  have hself : ∀ (x : Vv → S) (v : Vv), x ∈ nb x v :=
    fun x v => (hmem x x v).mpr fun w _ => rfl
  -- if `y` agrees with `x` off `v`, the two conditioning sets coincide
  have hnb_eq : ∀ (x y : Vv → S) (v : Vv), (∀ w : Vv, w ≠ v → y w = x w) →
      nb x v = nb y v := by
    intro x y v hxy
    ext z
    rw [hmem, hmem]
    constructor
    · intro h w hw; rw [h w hw, ← hxy w hw]
    · intro h w hw; rw [h w hw, hxy w hw]
  have hD_eq : ∀ (x y : Vv → S) (v : Vv), (∀ w : Vv, w ≠ v → y w = x w) →
      D x v = D y v := by
    intro x y v hxy
    rw [hD]
    simp only
    rw [hnb_eq x y v hxy]
  -- (1) nonnegativity
  have h1 : ∀ x y : Vv → S, 0 ≤ glauber π x y := by
    intro x y
    rw [hglauber]
    refine mul_nonneg (inv_nonneg.mpr hcardpos.le) (Finset.sum_nonneg fun v _ => ?_)
    by_cases h : ∀ w : Vv, w ≠ v → y w = x w
    · rw [if_pos h]
      exact div_nonneg (hπ.1 y) (hDnonneg x v)
    · rw [if_neg h]
  -- (2) rows at states of positive mass sum to one
  have h2 : ∀ x : Vv → S, 0 < π x → ∑ y, glauber π x y = 1 := by
    intro x hx
    have hDpos : ∀ v : Vv, 0 < D x v := by
      intro v
      rw [hD]
      simp only
      exact lt_of_lt_of_le hx
        (Finset.single_le_sum (f := fun z => π z) (fun z _ => hπ.1 z) (hself x v))
    rw [Finset.sum_congr rfl fun y _ => hglauber x y, ← Finset.mul_sum, Finset.sum_comm]
    have hinner : ∀ v : Vv,
        (∑ y, if ∀ w : Vv, w ≠ v → y w = x w then π y / D x v else 0) = 1 := by
      intro v
      have hsum : (∑ y, if ∀ w : Vv, w ≠ v → y w = x w then π y / D x v else 0)
          = ∑ y ∈ nb x v, π y / D x v := by
        rw [hnb]
        rw [Finset.sum_filter]
      rw [hsum]
      have hfold : ∑ y ∈ nb x v, π y / D x v = D x v / D x v := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        rfl
      rw [hfold]
      exact div_self (hDpos v).ne'
    rw [Finset.sum_congr rfl fun v _ => hinner v, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, inv_mul_cancel₀ hcardpos.ne']
  -- (3) reversibility
  have h3 : DetailedBalance (glauber π) π := by
    intro x y
    have key : π x * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → y w = x w then π y / D x v else 0)
        = π y * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → x w = y w then π x / D y v else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases h : ∀ w : Vv, w ≠ v → y w = x w
      · have h' : ∀ w : Vv, w ≠ v → x w = y w := fun w hw => (h w hw).symm
        rw [if_pos h, if_pos h', hD_eq x y v h]
        ring
      · have h' : ¬ (∀ w : Vv, w ≠ v → x w = y w) := fun hc =>
          h fun w hw => (hc w hw).symm
        rw [if_neg h, if_neg h', mul_zero, mul_zero]
    rw [hglauber x y, hglauber y x]
    calc π x * ((Fintype.card Vv : ℝ)⁻¹
          * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → y w = x w then π y / D x v else 0))
        = (Fintype.card Vv : ℝ)⁻¹
          * (π x * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → y w = x w then π y / D x v else 0)) := by
          ring
      _ = (Fintype.card Vv : ℝ)⁻¹
          * (π y * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → x w = y w then π x / D y v else 0)) := by
          rw [key]
      _ = π y * ((Fintype.card Vv : ℝ)⁻¹
          * ∑ v : Vv, (if ∀ w : Vv, w ≠ v → x w = y w then π x / D y v else 0)) := by
          ring
  -- (4) stationarity
  refine ⟨h1, h2, h3, hπ, ?_⟩
  funext y
  show ∑ x, π x * glauber π x y = π y
  rw [Finset.sum_congr rfl fun x _ => (h3 y x).symm, ← Finset.mul_sum]
  rcases eq_or_lt_of_le (hπ.1 y) with hy | hy
  · rw [← hy, zero_mul]
  · rw [h2 y hy, mul_one]
