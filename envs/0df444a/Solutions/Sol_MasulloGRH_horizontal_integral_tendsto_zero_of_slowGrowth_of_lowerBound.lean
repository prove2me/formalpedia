-- Prove2me | solution 1 for MasulloGRH.horizontal_integral_tendsto_zero_of_slowGrowth_of_lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @koffie
-- created : 2026-11-21T00:10:43.447858+00:00
-- url     : https://prove2.me/submissions/51539d22-9fb6-4abb-9b76-b087afbd1996

import Definitions.Def_MasulloGRH_MellinRpos
import Definitions.Def_MasulloGRH_SlowGrowthNearPoles

open Complex Filter Topology MasulloGRH

theorem solution (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ) (T : ℤ → ℝ) (hf : HasSlowGrowthNearPoles f a b T)
    (hT : ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧ ∀ k : ℤ, k ≠ 0 → c * |(k : ℝ)| ^ γ ≤ |T k|)
    (ε : ℝ) (hε : 0 < ε) (Φ : ℂ → ℂ)
    (hΦd : DifferentiableOn ℂ Φ (openStrip (a - ε) (b + ε)))
    (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε)) :
    Tendsto (fun k : ℤ => ∫ σ in a..b,
        ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖) cofinite (𝓝 0) := by
  obtain ⟨-, ⟨-, -, -, hTinf, -, -⟩, ⟨β, A, hβ, hA, hfb⟩, -⟩ := hf
  obtain ⟨c, γ, hc, hγ, hTlow⟩ := hT
  -- choose `N` with `N γ ≥ β + 1`
  obtain ⟨N, hN⟩ := exists_nat_ge ((β + 1) / γ)
  set N' := N + 1 with hN'
  have hNγ : β + 1 ≤ (N' : ℝ) * γ := by
    rw [div_le_iff₀ hγ] at hN
    have : (N : ℝ) * γ ≤ (N' : ℝ) * γ := by
      apply mul_le_mul_of_nonneg_right _ hγ.le; rw [hN']; push_cast; linarith
    linarith
  obtain ⟨C, hC, Y, hY⟩ := hΦ ε hε (by linarith) N' (by omega)
  -- the bounding sequence
  set B : ℤ → ℝ := fun k => (b - a) * (A * C * c⁻¹ ^ N') * |(k : ℝ)| ^ (β - N' * γ) with hB
  have hBlim : Tendsto B cofinite (𝓝 0) := by
    have h1 : Tendsto (fun k : ℤ => |(k : ℝ)|) cofinite atTop := by
      have : Tendsto (fun k : ℤ => |k|) cofinite atTop := by
        rw [Int.cofinite_eq]
        exact tendsto_sup.2 ⟨tendsto_abs_atBot_atTop, tendsto_abs_atTop_atTop⟩
      refine ((tendsto_intCast_atTop_atTop (R := ℝ)).comp this).congr fun k => ?_
      simp [Int.cast_abs]
    have h2 : Tendsto (fun x : ℝ => x ^ (β - N' * γ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (y := N' * γ - β) (by linarith)).congr fun x => by rw [neg_sub]
    simpa [hB] using (h2.comp h1).const_mul ((b - a) * (A * C * c⁻¹ ^ N'))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBlim
  · filter_upwards with k
    exact intervalIntegral.integral_nonneg hab.le fun _ _ => norm_nonneg _
  · have hev1 : ∀ᶠ k in cofinite, k ≠ (0 : ℤ) := eventually_cofinite_ne 0
    have hev2 : ∀ᶠ k in cofinite, max Y 1 ≤ |T k| := hTinf.eventually_ge_atTop _
    filter_upwards [hev1, hev2] with k hk0 hkY
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have hTpos : 0 < |T k| := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hkY)
    -- pointwise bound on the open segment
    have hpt : ∀ σ : ℝ, a < σ → σ < b →
        ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖ ≤
          A * |(k : ℝ)| ^ β * (C / |T k| ^ N') := by
      intro σ h1 h2
      rw [norm_mul]
      apply mul_le_mul (hfb k hk0 σ h1 h2) _ (norm_nonneg _) (by positivity)
      have := hY ((σ : ℂ) + (T k : ℂ) * I) (by simp; linarith) (by simp; linarith)
        (by simpa using le_trans (le_max_left _ _) hkY)
      simpa using this
    -- `|T k|^{-N'} ≤ c^{-N'} |k|^{-N' γ}`
    have hTpow : C / |T k| ^ N' ≤ C * c⁻¹ ^ N' * |(k : ℝ)| ^ (-(N' * γ)) := by
      have hlow := hTlow k hk0
      have hkγ : 0 < |(k : ℝ)| ^ γ := Real.rpow_pos_of_pos (by linarith) _
      have hpow : (c * |(k : ℝ)| ^ γ) ^ N' ≤ |T k| ^ N' :=
        pow_le_pow_left₀ (by positivity) hlow N'
      have e1 : |(k : ℝ)| ^ (-((N' : ℝ) * γ)) = ((|(k : ℝ)| ^ γ) ^ N')⁻¹ := by
        rw [Real.rpow_neg (abs_nonneg _), mul_comm, Real.rpow_mul_natCast (abs_nonneg _)]
      have e2 : C * c⁻¹ ^ N' * ((|(k : ℝ)| ^ γ) ^ N')⁻¹ = C / (c * |(k : ℝ)| ^ γ) ^ N' := by
        rw [mul_pow, inv_pow]; field_simp
      rw [e1, e2]
      exact div_le_div_of_nonneg_left hC.le (by positivity) hpow
    have hbound : ∀ σ : ℝ, a < σ → σ < b →
        ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖ ≤
          (A * C * c⁻¹ ^ N') * |(k : ℝ)| ^ (β - N' * γ) := by
      intro σ h1 h2
      refine (hpt σ h1 h2).trans ?_
      have hsplit : |(k : ℝ)| ^ (β - N' * γ) = |(k : ℝ)| ^ β * |(k : ℝ)| ^ (-(N' * γ)) := by
        rw [← Real.rpow_add (by linarith)]; ring_nf
      rw [hsplit]
      calc A * |(k : ℝ)| ^ β * (C / |T k| ^ N')
          ≤ A * |(k : ℝ)| ^ β * (C * c⁻¹ ^ N' * |(k : ℝ)| ^ (-(N' * γ))) :=
            mul_le_mul_of_nonneg_left hTpow (by positivity)
        _ = A * C * c⁻¹ ^ N' * (|(k : ℝ)| ^ β * |(k : ℝ)| ^ (-(N' * γ))) := by ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le (a := a) (b := b) hab.le
      (f := fun σ : ℝ => ‖f ((σ : ℂ) + (T k : ℂ) * I) * Φ ((σ : ℂ) + (T k : ℂ) * I)‖)
      (g := fun _ => (A * C * c⁻¹ ^ N') * |(k : ℝ)| ^ (β - N' * γ)) (μ := MeasureTheory.volume) ?_
      intervalIntegrable_const
    · simp only [intervalIntegral.integral_const, smul_eq_mul] at hint
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine hint.trans (le_of_eq ?_)
      simp only [hB]; ring
    · have : ∀ᵐ σ : ℝ ∂MeasureTheory.volume, σ ≠ b := MeasureTheory.Measure.ae_ne _ b
      filter_upwards [this] with σ hσb hσ
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hbound σ hσ.1 (lt_of_le_of_ne hσ.2 hσb)
