-- Prove2me | solution 1 for LogLogJam.Supplement.split_readout_accuracy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:28:47.386849+00:00
-- url     : https://prove2.me/submissions/a798e880-8e4d-4017-9b2b-08d1b61ea260
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_transcriptLaw
import Theorems.Thm_LogLogJam_Supplement_fixed_angle_accuracy
import Theorems.Thm_LogLogJam_Supplement_fixed_count_accuracy
import Theorems.Thm_LogLogJam_Supplement_fixed_phase_count_scheme

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open LogLogJam LogLogJam.Supplement

/-- The measurements and two statistical guarantees from Lemmas 8.26 and 8.27,
with the raw photon-mean error still in its natural units. Neither estimator
returns a density operator. -/
theorem solution :
    ∃ C > (0 : ℝ), ∀ η δ : ℝ, 0 < η → η ≤ 1 / 4 → 0 < δ → δ < 1 →
    ∀ m : ℕ, C * Real.log (2 / δ) / η ^ 2 ≤ m →
    ∃ (S : BosonicLearn.AdaptiveScheme 1 m ℝ)
      (angle mean : (Fin m → ℝ) → ℝ),
      phaseCountReadouts S ∧ Measurable angle ∧ Measurable mean ∧
      (∀ x, 0 ≤ mean x) ∧
      (∀ x y, (∀ i : Fin m, i.val < m / 2 → x i = y i) → angle x = angle y) ∧
      (∀ x y, (∀ i : Fin m, m / 2 ≤ i.val → x i = y i) → mean x = mean y) ∧
      ∀ (ρ : State (Occupation (Fin 1))) (r θ : ℝ), squeezedAt ρ r θ →
      (BosonicLearn.transcriptLaw S ρ.coefficients
        {x | η < LogLogJam.trDist (Real.exp (2 * r)) θ (angle x)} ≤ ENNReal.ofReal δ) ∧
      (BosonicLearn.transcriptLaw S ρ.coefficients
        {x | η * Real.cosh r * Real.sinh r < |mean x - Real.sinh r ^ 2|} ≤ ENNReal.ofReal δ)  := by
  obtain ⟨U, hU, angleGood⟩ := fixed_angle_accuracy
  obtain ⟨V, hV, countGood⟩ := fixed_count_accuracy
  refine ⟨max U V, lt_of_lt_of_le hU (le_max_left _ _), ?_⟩
  intro η δ hη hs hδ hd m hm
  have hlog : 0 ≤ Real.log (2 / δ) := Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hbudget (W : ℝ) (hw : W ≤ max U V) : W * Real.log (2 / δ) / η ^ 2 ≤ m :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw hlog) (sq_nonneg η)).trans hm
  obtain ⟨S, hS⟩ := fixed_phase_count_scheme m
  obtain ⟨a, ha, hfirst, hang⟩ := angleGood η δ hη hs hδ hd m (hbudget U (le_max_left _ _)) S hS
  obtain ⟨μ, hμ, hnonneg, hlast, hcount⟩ := countGood η δ hη hs hδ hd m (hbudget V (le_max_right _ _)) S hS
  exact ⟨S, a, μ, hS, ha, hμ, hnonneg, hfirst, hlast, fun ρ r θ h => ⟨hang ρ r θ h, hcount ρ r θ h⟩⟩
