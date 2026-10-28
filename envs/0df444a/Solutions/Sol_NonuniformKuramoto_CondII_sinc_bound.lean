-- Prove2me | solution 1 for NonuniformKuramoto.CondII.sinc_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:41:02.596686+00:00
-- url     : https://prove2.me/submissions/6216d7f8-0fa3-4498-b532-259f7636fdc2

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondII_Graph
import Definitions.Def_NonuniformKuramoto_CondII_Model
import Definitions.Def_NonuniformKuramoto_CondII_Constants
open Matrix

namespace Aux_NonuniformKuramoto_CondII_sinc_bound
open NonuniformKuramoto.CondII

theorem Hmul {n : ℕ} (x : Fin n → ℝ) (p : Pairs n) :
    (incH n *ᵥ x) p = x p.1.2 - x p.1.1 := by
  have hne : p.1.2 ≠ p.1.1 := ne_of_gt p.2
  simp only [mulVec, dotProduct, incH]
  rw [Fintype.sum_eq_add p.1.2 p.1.1 hne]
  · rw [if_pos rfl, if_neg (Ne.symm hne), if_pos rfl]; ring
  · intro c hc
    rw [if_neg hc.1, if_neg hc.2, zero_mul]


theorem sin_div_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ Real.pi) :
    Real.sin y / y ≤ Real.sin x / x := by
  have hy0 : 0 < y := lt_of_lt_of_le hx hxy
  have hc := strictConcaveOn_sin_Icc.concaveOn
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hyI : y ∈ Set.Icc 0 Real.pi := ⟨hy0.le, hy⟩
  have ha : 0 ≤ 1 - x / y := by rw [sub_nonneg, div_le_one hy0]; exact hxy
  have hb : 0 ≤ x / y := div_nonneg hx.le hy0.le
  have := hc.2 h0 hyI ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at this
  have e : x / y * y = x := by field_simp
  rw [e] at this
  rw [div_le_div_iff₀ hy0 hx]
  have := mul_le_mul_of_nonneg_right this hy0.le
  have e2 : x / y * Real.sin y * y = x * Real.sin y := by field_simp
  rw [e2] at this
  linarith

theorem sinc_abs (d : ℝ) : Real.sinc |d| = Real.sinc d := by
  rcases le_or_gt 0 d with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, Real.sinc_neg]

end Aux_NonuniformKuramoto_CondII_sinc_bound

open NonuniformKuramoto.CondII Aux_NonuniformKuramoto_CondII_sinc_bound in
theorem solution {n : ℕ} (ρ : ℝ) (hρ0 : 0 < ρ) (hρπ : ρ < Real.pi) (θ : Fin n → ℝ)
    (hθ : NonuniformKuramoto.CondI.ArcOpen Real.pi θ) (hθρ : normH θ ≤ ρ) (i j : Fin n) :
    |θ i - θ j| ≤ normH θ ∧ |θ i - θ j| ≤ ρ ∧
      Real.sinc (θ i - θ j) ≤ 1 ∧ Real.sinc ρ ≤ Real.sinc (θ i - θ j) ∧
      (θ i - θ j) ^ 2 * Real.sinc ρ ≤ (θ i - θ j) * Real.sin (θ i - θ j) := by
  have h1 : |θ i - θ j| ≤ normH θ := by
    unfold normH euclNorm
    apply Real.abs_le_sqrt
    have hnn : ∀ p : Pairs n, 0 ≤ (incH n *ᵥ θ) p ^ 2 := fun p => sq_nonneg _
    rcases lt_trichotomy i j with h | h | h
    · have := Finset.single_le_sum (f := fun p : Pairs n => (incH n *ᵥ θ) p ^ 2)
        (fun p _ => hnn p) (Finset.mem_univ (⟨(i, j), h⟩ : Pairs n))
      simp only [Hmul] at this ⊢
      calc (θ i - θ j) ^ 2 = (θ j - θ i) ^ 2 := by ring
        _ ≤ _ := this
    · subst h
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact Finset.sum_nonneg fun p _ => hnn p
    · have := Finset.single_le_sum (f := fun p : Pairs n => (incH n *ᵥ θ) p ^ 2)
        (fun p _ => hnn p) (Finset.mem_univ (⟨(j, i), h⟩ : Pairs n))
      simp only [Hmul] at this ⊢
      exact this
  have h2 : |θ i - θ j| ≤ ρ := h1.trans hθρ
  have h4 : Real.sinc ρ ≤ Real.sinc (θ i - θ j) := by
    rw [← sinc_abs (θ i - θ j)]
    rcases (abs_nonneg (θ i - θ j)).eq_or_lt with h | h
    · rw [← h, Real.sinc_zero]; exact Real.sinc_le_one _
    · rw [Real.sinc_of_ne_zero hρ0.ne', Real.sinc_of_ne_zero h.ne']
      exact sin_div_anti h h2 hρπ.le
  refine ⟨h1, h2, Real.sinc_le_one _, h4, ?_⟩
  have e : (θ i - θ j) * Real.sin (θ i - θ j) = (θ i - θ j) ^ 2 * Real.sinc (θ i - θ j) := by
    by_cases hd : θ i - θ j = 0
    · rw [hd]; simp
    · rw [Real.sinc_of_ne_zero hd]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
