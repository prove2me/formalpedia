-- Prove2me | solution 1 for NonuniformKuramoto.CondI.dini_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:12:29.115295+00:00
-- url     : https://prove2.me/submissions/b761634b-b82e-459b-acf9-43bf5577d1ed

import Mathlib
import Definitions.Def_NonuniformKuramoto_CondI_Model
import Definitions.Def_NonuniformKuramoto_CondI_Constants

namespace Aux_NonuniformKuramoto_CondI_dini

theorem sin_chord {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.pi) (hy0 : 0 < y) :
    x / y * Real.sin y ≤ Real.sin x := by
  have hc := strictConcaveOn_sin_Icc.concaveOn
  have h0 : (0 : ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_rfl, Real.pi_pos.le⟩
  have hyI : y ∈ Set.Icc 0 Real.pi := ⟨hy0.le, hy⟩
  have ha : 0 ≤ 1 - x / y := by rw [sub_nonneg, div_le_one hy0]; exact hxy
  have hb : 0 ≤ x / y := div_nonneg hx hy0.le
  have := hc.2 h0 hyI ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at this
  have e : x / y * y = x := by field_simp
  rwa [e] at this

theorem sin_add_sub {u γ : ℝ} (hu0 : 0 ≤ u) (huγ : u ≤ γ) (hγ : γ ≤ Real.pi) :
    Real.sin γ ≤ Real.sin u + Real.sin (γ - u) := by
  rcases (hu0.trans huγ).eq_or_lt with h | h
  · rw [← h] at huγ ⊢
    have : u = 0 := le_antisymm huγ hu0
    subst this; simp
  · have h1 := sin_chord hu0 huγ hγ h
    have h2 := sin_chord (by linarith : 0 ≤ γ - u) (by linarith) hγ h
    have : u / γ * Real.sin γ + (γ - u) / γ * Real.sin γ = Real.sin γ := by
      field_simp
      ring
    linarith

end Aux_NonuniformKuramoto_CondI_dini

open NonuniformKuramoto.CondI Aux_NonuniformKuramoto_CondI_dini in
theorem solution {n : ℕ} (hn : 2 ≤ n) (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i)
    (hP : ∀ i j, i ≠ j → 0 < P i j) (hPii : ∀ i, P i i = 0) (hϕii : ∀ i, ϕ i i = 0)
    (hϕ : ∀ i j, i ≠ j → 0 ≤ ϕ i j ∧ ϕ i j < Real.pi / 2)
    (θ : Fin n → ℝ) (m ℓ : Fin n) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγπ : γ ≤ Real.pi)
    (hmℓ : θ m - θ ℓ = γ) (hk : ∀ k, θ ℓ ≤ θ k ∧ θ k ≤ θ m) :
    field D ω P ϕ θ m - field D ω P ϕ θ ℓ ≤
      omegaSpread D ω - GammaMin D P ϕ * Real.sin γ + 2 * lossMax D P ϕ := by
  classical
  have hpi := Real.pi_pos
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hoff : (Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2)).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.ext_iff]⟩
  have hϕlt : ∀ i j, ϕ i j < Real.pi / 2 := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hϕii]; linarith
    · exact (hϕ i j h).2
  have hϕnn : ∀ i j, 0 ≤ ϕ i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hϕii]
    · exact (hϕ i j h).1
  have hPnn : ∀ i j, 0 ≤ P i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hPii]
    · exact (hP i j h).le
  set b : Fin n → Fin n → ℝ := fun i j => P i j / D i * Real.cos (ϕ i j) with hb
  set c : Fin n → Fin n → ℝ := fun i j => P i j / D i * Real.sin (ϕ i j) with hc
  have hc0 : ∀ i j, 0 ≤ c i j := fun i j => mul_nonneg (div_nonneg (hPnn i j) (hD i).le)
    (Real.sin_nonneg_of_nonneg_of_le_pi (hϕnn i j) (by linarith [hϕlt i j]))
  set μ := minOffDiag (fun p : Fin n × Fin n => P p.1 p.2 / D p.1 * Real.cos (ϕ p.1 p.2)) with hμ
  have hμle : ∀ i j, i ≠ j → μ ≤ b i j := by
    intro i j hij
    rw [hμ]; unfold minOffDiag; rw [dif_pos hoff]
    exact Finset.inf'_le (fun p : Fin n × Fin n => P p.1 p.2 / D p.1 * Real.cos (ϕ p.1 p.2))
      (Finset.mem_filter.mpr ⟨Finset.mem_univ (i, j), hij⟩)
  have hμpos : 0 < μ := by
    rw [hμ]; unfold minOffDiag; rw [dif_pos hoff, Finset.lt_inf'_iff]
    intro p hp
    have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact mul_pos (div_pos (hP _ _ hp') (hD _))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hϕnn p.1 p.2], hϕlt p.1 p.2⟩)
  have hGM : GammaMin D P ϕ = n * μ := rfl
  -- decomposition of the field
  have hfield : ∀ i, field D ω P ϕ θ i =
      ω i / D i - ∑ k, b i k * Real.sin (θ i - θ k) - ∑ k, c i k * Real.cos (θ i - θ k) := by
    intro i
    unfold field
    rw [sub_div, Finset.sum_div, sub_sub, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hb, hc]
    rw [Real.sin_add]
    ring
  rw [hfield m, hfield ℓ]
  -- ω part
  have hω : ω m / D m - ω ℓ / D ℓ ≤ omegaSpread D ω := by
    unfold omegaSpread maxOffDiag
    rw [dif_pos hoff]
    by_cases hml : m = ℓ
    · subst hml
      rw [sub_self]
      obtain ⟨p, hp⟩ := hoff
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun p : Fin n × Fin n =>
        |ω p.1 / D p.1 - ω p.2 / D p.2|) hp)
    · exact le_trans (le_abs_self _) (Finset.le_sup' (fun p : Fin n × Fin n =>
        |ω p.1 / D p.1 - ω p.2 / D p.2|) (Finset.mem_filter.mpr ⟨Finset.mem_univ (m, ℓ), hml⟩))
  -- lossy part
  have hloss : ∀ i, |∑ k, c i k * Real.cos (θ i - θ k)| ≤ lossMax D P ϕ := by
    intro i
    have h1 : |∑ k, c i k * Real.cos (θ i - θ k)| ≤ ∑ k, c i k := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, abs_of_nonneg (hc0 i k)]
      exact mul_le_of_le_one_right (hc0 i k) (Real.abs_cos_le_one _)
    refine h1.trans ?_
    unfold lossMax maxIdx
    rw [dif_pos hne]
    exact Finset.le_sup' (fun i => ∑ j, P i j / D i * Real.sin (ϕ i j)) (Finset.mem_univ i)
  have hlm := abs_le.mp (hloss m)
  have hll := abs_le.mp (hloss ℓ)
  -- coupling part
  have hcoup : ∀ k, μ * Real.sin γ ≤ b m k * Real.sin (θ m - θ k) - b ℓ k * Real.sin (θ ℓ - θ k) := by
    intro k
    obtain ⟨hk1, hk2⟩ := hk k
    set u := θ m - θ k with hu
    have hu0 : 0 ≤ u := by rw [hu]; linarith
    have huγ : u ≤ γ := by rw [hu, ← hmℓ]; linarith
    have hγu : θ ℓ - θ k = -(γ - u) := by rw [hu, ← hmℓ]; ring
    rw [hγu, Real.sin_neg]
    have hs1 : 0 ≤ Real.sin u := Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith)
    have hs2 : 0 ≤ Real.sin (γ - u) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have e1 : μ * Real.sin u ≤ b m k * Real.sin u := by
      by_cases h : m = k
      · subst h
        have : u = 0 := by rw [hu]; ring
        rw [this, Real.sin_zero, mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right (hμle m k h) hs1
    have e2 : μ * Real.sin (γ - u) ≤ b ℓ k * Real.sin (γ - u) := by
      by_cases h : ℓ = k
      · subst h
        have : γ - u = 0 := by rw [hu, ← hmℓ]; ring
        rw [this, Real.sin_zero, mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right (hμle ℓ k h) hs2
    have e3 := mul_le_mul_of_nonneg_left (sin_add_sub hu0 huγ hγπ) hμpos.le
    linarith
  have hsum : (n : ℝ) * μ * Real.sin γ ≤
      ∑ k, b m k * Real.sin (θ m - θ k) - ∑ k, b ℓ k * Real.sin (θ ℓ - θ k) := by
    rw [← Finset.sum_sub_distrib]
    calc (n : ℝ) * μ * Real.sin γ = ∑ _k : Fin n, μ * Real.sin γ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hcoup k
  rw [hGM]
  linarith
