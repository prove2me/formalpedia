-- Prove2me | solution 1 for HunterPDE.Compactness.weakDeriv_eLpNorm_le_sobolevNorm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:10:36.335339+00:00
-- url     : https://prove2.me/submissions/6dec8ef9-ba53-49c5-8a4c-98a71c67499f

import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_ae_eq
import Definitions.Def_HunterPDE_Compactness_Sobolev
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory HunterPDE.Compactness HunterPDE.Shared
open scoped ENNReal
set_option autoImplicit false

theorem solution {n k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (α : Fin n → ℕ) (hα : α ∈ multiIndicesLe n k)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : HasWeakDeriv Ω α f g) :
    eLpNorm g p (volume.restrict Ω) ≤ sobolevNorm k p Ω f := by
  classical
  have hex : ∃ g, HasWeakDeriv Ω α f g := ⟨g, hg⟩
  have hc : HasWeakDeriv Ω α f (weakDeriv Ω α f) := by
    simpa only [weakDeriv, dif_pos hex] using hex.choose_spec
  rw [← eLpNorm_congr_ae (hc.ae_eq hΩ hg)]
  have hr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'
  have hb := ENNReal.rpow_le_rpow
    (Finset.single_le_sum (fun β _ => show 0 ≤ eLpNorm (weakDeriv Ω β f) p
      (volume.restrict Ω) ^ p.toReal from zero_le) hα) (one_div_nonneg.mpr hr.le)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hr.ne', ENNReal.rpow_one] at hb
  simpa only [sobolevNorm, if_neg hp'] using hb
