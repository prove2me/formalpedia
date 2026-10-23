-- Prove2me | solution 1 for KellyStochasticNetworks.EffectiveBandwidth.largest_term
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:11:05.747571+00:00
-- url     : https://prove2.me/submissions/0b5da7a3-1ecf-4cee-8300-b6fb07919078

import Mathlib

open Filter Topology
open scoped BigOperators

theorem g78e_inv (C : ℝ) :
    Tendsto (fun N : ℕ => C / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)

theorem solution :
    (∀ (aSeq bSeq : ℕ → ℝ) (a b : ℝ),
      (∀ N, 0 < aSeq N) → (∀ N, 0 < bSeq N) → b ≤ a →
      Tendsto (fun N : ℕ => Real.log (aSeq N) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 a) →
      Tendsto (fun N : ℕ => Real.log (bSeq N) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 b) →
      Tendsto (fun N : ℕ => Real.log (aSeq N + bSeq N) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 a)) ∧
    (∀ (T : ℕ) (p : Fin (T + 1) → ℕ → ℝ) (r : Fin (T + 1) → ℝ),
      (∀ t N, 0 < p t N) →
      (∀ t, Tendsto (fun N : ℕ => Real.log (p t N) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 (r t))) →
      Tendsto (fun N : ℕ => Real.log (∑ t, p t N) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 (Finset.univ.sup' Finset.univ_nonempty r))) := by
  have hNpos : ∀ N : ℕ, (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := fun N => by positivity
  refine ⟨fun aSeq bSeq a b ha hb hba hA hB => ?_, fun T p r hp hr => ?_⟩
  · set M : ℕ → ℝ := fun N => max (Real.log (aSeq N) / ((N + 1 : ℕ) : ℝ))
      (Real.log (bSeq N) / ((N + 1 : ℕ) : ℝ))
    have hM : Tendsto M atTop (𝓝 a) := by
      have := hA.max hB
      rwa [max_eq_left hba] at this
    have hup : Tendsto (fun N => M N + Real.log 2 / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 a) := by
      simpa using hM.add (g78e_inv (Real.log 2))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hA hup (fun N => ?_) (fun N => ?_)
    · simp only
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (ha N) (by linarith [hb N])) (hNpos N).le
    · simp only
      have h1 : Real.log (aSeq N) ≤ ((N + 1 : ℕ) : ℝ) * M N := by
        have := le_max_left (Real.log (aSeq N) / ((N + 1 : ℕ) : ℝ))
          (Real.log (bSeq N) / ((N + 1 : ℕ) : ℝ))
        rw [div_le_iff₀ (hNpos N)] at this; linarith
      have h2 : Real.log (bSeq N) ≤ ((N + 1 : ℕ) : ℝ) * M N := by
        have := le_max_right (Real.log (aSeq N) / ((N + 1 : ℕ) : ℝ))
          (Real.log (bSeq N) / ((N + 1 : ℕ) : ℝ))
        rw [div_le_iff₀ (hNpos N)] at this; linarith
      have e1 : aSeq N ≤ Real.exp (((N + 1 : ℕ) : ℝ) * M N) := by
        rw [← Real.exp_log (ha N)]; exact Real.exp_le_exp.2 h1
      have e2 : bSeq N ≤ Real.exp (((N + 1 : ℕ) : ℝ) * M N) := by
        rw [← Real.exp_log (hb N)]; exact Real.exp_le_exp.2 h2
      have hs : Real.log (aSeq N + bSeq N) ≤ Real.log 2 + ((N + 1 : ℕ) : ℝ) * M N := by
        have : aSeq N + bSeq N ≤ 2 * Real.exp (((N + 1 : ℕ) : ℝ) * M N) := by linarith
        have := Real.log_le_log (by linarith [ha N, hb N]) this
        rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
      rw [div_le_iff₀ (hNpos N), add_mul, div_mul_cancel₀ _ (hNpos N).ne']
      linarith
  · have hne : (Finset.univ : Finset (Fin (T + 1))).Nonempty := Finset.univ_nonempty
    set f : Fin (T + 1) → ℕ → ℝ := fun t N => Real.log (p t N) / ((N + 1 : ℕ) : ℝ)
    have hM := Tendsto.finset_sup'_nhds (f := f) (l := atTop) (g := r) hne (fun t _ => hr t)
    set M := Finset.univ.sup' hne f
    have hMN : ∀ N, M N = Finset.univ.sup' hne (fun t => f t N) := fun N =>
      Finset.sup'_apply hne f N
    have hup : Tendsto (fun N => M N + Real.log ((T : ℝ) + 1) / ((N + 1 : ℕ) : ℝ)) atTop
        (𝓝 (Finset.univ.sup' hne r)) := by
      simpa using hM.add (g78e_inv (Real.log ((T : ℝ) + 1)))
    have hsum : ∀ N, 0 < ∑ t, p t N := fun N =>
      Finset.sum_pos (fun t _ => hp t N) hne
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hM hup (fun N => ?_) (fun N => ?_)
    · show M N ≤ _
      rw [hMN]
      refine Finset.sup'_le hne _ fun t _ => ?_
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (hp t N) (Finset.single_le_sum (fun t _ => (hp t N).le)
          (Finset.mem_univ t))) (hNpos N).le
    · simp only
      have h1 : ∀ t, p t N ≤ Real.exp (((N + 1 : ℕ) : ℝ) * M N) := by
        intro t
        have : f t N ≤ M N := by rw [hMN]; exact Finset.le_sup' (fun t => f t N) (Finset.mem_univ t)
        simp only [f] at this
        rw [div_le_iff₀ (hNpos N)] at this
        rw [← Real.exp_log (hp t N)]
        exact Real.exp_le_exp.2 (by linarith)
      have hs : ∑ t, p t N ≤ ((T : ℝ) + 1) * Real.exp (((N + 1 : ℕ) : ℝ) * M N) := by
        calc ∑ t, p t N ≤ ∑ _t : Fin (T + 1), Real.exp (((N + 1 : ℕ) : ℝ) * M N) :=
              Finset.sum_le_sum fun t _ => h1 t
          _ = _ := by simp
      have hl := Real.log_le_log (hsum N) hs
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hl
      rw [div_le_iff₀ (hNpos N), add_mul, div_mul_cancel₀ _ (hNpos N).ne']
      linarith
