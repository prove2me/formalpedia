-- Prove2me | solution 1 for OAI.PiExponent.pi_approximation_determinant_sequences
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T19:12:32.837749+00:00
-- url     : https://prove2.me/submissions/033cfaaa-7a8c-4c6a-a02f-e67d90b7df01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_pi_cofinal_real_height_determinant_certificates

open Filter Topology

-- Sampling cofinal certificates requires no monotonicity or continuity of
-- the height-dependent quantities. Both limits pull back along the same heights.
private theorem sample_cofinal_certificates
    (nu theta x ear ean collisionLimit : ℝ)
    (mean error rate : ℝ → ℝ)
    (herror : Tendsto error atTop (𝓝 0))
    (hrate : Tendsto rate atTop (𝓝 collisionLimit))
    (hcofinal : ∀ L : ℝ, ∃ H D : ℝ,
      L ≤ H ∧ 0 < H ∧ 0 ≤ mean H ∧ mean H ≤ theta ∧
      -(1 - mean H) - ear ≤ D ∧
      D ≤ ean + error H + max (-rate H) (-nu * (x - mean H))) :
    ∃ b d err collision : ℕ → ℝ,
      Tendsto err atTop (𝓝 0) ∧
      Tendsto collision atTop (𝓝 collisionLimit) ∧
      (∀ᶠ n in atTop, 0 ≤ b n) ∧
      (∀ᶠ n in atTop, b n ≤ theta) ∧
      (∀ᶠ n in atTop, -(1 - b n) - ear ≤ d n) ∧
      (∀ᶠ n in atTop,
        d n ≤ ean + err n + max (-collision n) (-nu * (x - b n))) := by
  classical
  have hex : ∀ n : ℕ, ∃ H D : ℝ,
      (n : ℝ) ≤ H ∧ 0 < H ∧ 0 ≤ mean H ∧ mean H ≤ theta ∧
      -(1 - mean H) - ear ≤ D ∧
      D ≤ ean + error H + max (-rate H) (-nu * (x - mean H)) :=
    fun n => hcofinal (n : ℝ)
  choose H D hheight hpos hnonneg hmean hlower hupper using hex
  have hH : Tendsto H atTop atTop :=
    tendsto_atTop_mono hheight tendsto_natCast_atTop_atTop
  refine ⟨mean ∘ H, D, error ∘ H, rate ∘ H,
    herror.comp hH, hrate.comp hH, ?_, ?_, ?_, ?_⟩
  · exact Eventually.of_forall hnonneg
  · exact Eventually.of_forall hmean
  · exact Eventually.of_forall hlower
  · exact Eventually.of_forall hupper

theorem solution
    (nu : ℝ) (hnu : 2 < nu)
    (hbad : ∀ Q : ℕ, ∃ (p : ℤ) (q : ℕ),
      Q ≤ q ∧ |Real.pi - (p : ℝ) / (q : ℝ)| ≤ (q : ℝ) ^ (-nu)) :
    ∃ theta x ear ean collisionLimit : ℝ,
      ∃ b d err collision : ℕ → ℝ,
        ear + ean < nu * (x - theta) - (1 - theta) ∧
        1 + ear + ean < collisionLimit ∧
        Tendsto err atTop (𝓝 0) ∧
        Tendsto collision atTop (𝓝 collisionLimit) ∧
        (∀ᶠ n in atTop, 0 ≤ b n) ∧
        (∀ᶠ n in atTop, b n ≤ theta) ∧
        (∀ᶠ n in atTop, -(1 - b n) - ear ≤ d n) ∧
        (∀ᶠ n in atTop,
          d n ≤ ean + err n + max (-collision n) (-nu * (x - b n))) := by
  obtain ⟨theta, x, ear, ean, collisionLimit, mean, error, rate,
    hgap, hcollision, herror, hrate, hcofinal⟩ :=
    OAI.PiExponent.pi_cofinal_real_height_determinant_certificates nu hnu hbad
  obtain ⟨b, d, err, collision, herr, hcol, hb0, hb, hlower, hupper⟩ :=
    sample_cofinal_certificates nu theta x ear ean collisionLimit
      mean error rate herror hrate hcofinal
  exact ⟨theta, x, ear, ean, collisionLimit, b, d, err, collision,
    hgap, hcollision, herr, hcol, hb0, hb, hlower, hupper⟩
