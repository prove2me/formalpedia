-- Prove2me | solution 1 for MasulloGRH.weighted_L2_to_L1_positiveHaar
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:08:23.142203+00:00
-- url     : https://prove2.me/submissions/f93b1842-cb39-47ab-9869-709d31dcb758

import Theorems.Thm_MasulloGRH_sobolev_jet_weight_integrable_iff
import Mathlib.MeasureTheory.Function.L2Space
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal

private theorem weighted_real (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ f : ℝ → ℂ,
      MemLp (fun x => ((1 + x ^ 2) ^ (s / 4) : ℝ) • f x) 2 volume →
      Integrable f ∧ eLpNorm f 1 volume ≤
        C * eLpNorm (fun x => ((1 + x ^ 2) ^ (s / 4) : ℝ) • f x) 2 volume := by
  let g : ℝ → ℝ := fun x => (1 + x ^ 2) ^ (-s / 4)
  have hgcont : Continuous g := by
    dsimp [g]
    apply Continuous.rpow_const (by fun_prop)
    intro x
    exact Or.inl (ne_of_gt (by positivity : 0 < 1 + x ^ 2))
  have hg : MemLp g 2 volume := by
    apply (memLp_two_iff_integrable_sq hgcont.aestronglyMeasurable).mpr
    have heq : (fun x => g x ^ 2) =
        (fun x : ℝ => x ^ (2 * 0) / (1 + x ^ 2) ^ (s / 2)) := by
      funext x
      dsimp [g]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1 + x ^ 2)]
      norm_num only [Nat.cast_ofNat]
      have hp : (-s / 4) * (2 : ℝ) = -(s / 2) := by ring
      rw [hp, Real.rpow_neg (by positivity : 0 ≤ 1 + x ^ 2)]
      simp
    rw [heq]
    exact (MasulloGRH.sobolev_jet_weight_integrable_iff 0 s hs).mpr (by simpa using hs)
  let C := eLpNorm g 2 volume + 1
  refine ⟨C, by dsimp [C]; positivity,
    ENNReal.add_lt_top.mpr ⟨hg.2, by norm_num⟩, ?_⟩
  intro f hf
  let F : ℝ → ℂ := fun x => ((1 + x ^ 2) ^ (s / 4) : ℝ) • f x
  have heq : g • F = f := by
    funext x
    simp only [Pi.smul_apply', F, g, smul_smul]
    rw [← Real.rpow_add (by positivity : 0 < 1 + x ^ 2)]
    have hzero : -s / 4 + s / 4 = 0 := by ring
    rw [hzero, Real.rpow_zero, one_smul]
  have hmem : MemLp (g • F) 1 volume := hf.smul hg
  refine ⟨memLp_one_iff_integrable.mp (heq ▸ hmem), ?_⟩
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf.1 hg.1
  rw [heq] at h
  exact h.trans (mul_le_mul' (le_add_right le_rfl) le_rfl)

theorem solution (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ f : ℝ → ℂ,
      MemLp (fun t => ((1 + (Real.log t) ^ 2) ^ (s / 4) : ℝ) • f t)
        2 (Measure.map Real.exp volume) →
      Integrable f (Measure.map Real.exp volume) ∧
      eLpNorm f 1 (Measure.map Real.exp volume) ≤
        C * eLpNorm (fun t => ((1 + (Real.log t) ^ 2) ^ (s / 4) : ℝ) • f t)
          2 (Measure.map Real.exp volume) := by
  have he : MeasurableEmbedding Real.exp := Real.isOpenEmbedding_exp.measurableEmbedding
  obtain ⟨C, hC, hCt, h⟩ := weighted_real s hs
  refine ⟨C, hC, hCt, ?_⟩
  intro f hf
  have hf' : MemLp (fun x => ((1 + x ^ 2) ^ (s / 4) : ℝ) • (f ∘ Real.exp) x) 2 volume := by
    simpa only [Function.comp_def, Real.log_exp] using he.memLp_map_measure_iff.mp hf
  obtain ⟨hi, hb⟩ := h (f ∘ Real.exp) hf'
  refine ⟨he.integrable_map_iff.mpr hi, ?_⟩
  simp only [he.eLpNorm_map_measure, Function.comp_def, Real.log_exp]
  exact hb
