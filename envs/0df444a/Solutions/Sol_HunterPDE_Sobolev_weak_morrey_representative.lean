-- Prove2me | solution 1 for HunterPDE.Sobolev.weak_morrey_representative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-18T17:24:08.47003+00:00
-- url     : https://prove2.me/submissions/0a92530c-1c20-49f0-b083-6ff1698e5223

import Theorems.Thm_HunterPDE_Sobolev_morrey_increment_of_contDiff
import Theorems.Thm_HunterPDE_Sobolev_exists_smooth_ae_approx_gradient_bound
import Theorems.Thm_MeasureTheory_exists_holder_representative_of_ae_tendsto
import Mathlib.Tactic.Linarith

open MeasureTheory
open scoped ENNReal NNReal

theorem solution {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ) (hnp : (n : ℝ) < p) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
        HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧
          MemLp g (ENNReal.ofReal p) volume) →
      ∀ C : ℝ≥0,
        eLpNorm (HunterPDE.Shared.weakGradNorm Set.univ f) (ENNReal.ofReal p) volume ≤
          (C : ℝ≥0∞) →
      ∃ u : EuclideanSpace ℝ (Fin n) → ℝ, Continuous u ∧ u =ᵐ[volume] f ∧
        ∀ x y, dist (u x) (u y) ≤ (A : ℝ) * (C : ℝ) *
          dist x y ^ (1 - (n : ℝ) / p) := by
  classical
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ p := (hnreal.trans_lt hnp).le
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hα : 0 < 1 - (n : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hnp)
  obtain ⟨A, hA⟩ := HunterPDE.Sobolev.morrey_increment_of_contDiff hnp
  refine ⟨A, fun f hf C hC => ?_⟩
  obtain ⟨v, hv, hgrad, hae⟩ :=
    HunterPDE.Sobolev.exists_smooth_ae_approx_gradient_bound hn p hp f hf C hC
  apply MeasureTheory.exists_holder_representative_of_ae_tendsto volume (A * C)
    (1 - (n : ℝ) / p) hα v f _ hae
  intro j x y
  have h : ENNReal.ofReal |v j x - v j y| ≤
      (A : ℝ≥0∞) * (C : ℝ≥0∞) * ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ) / p)) := by
    apply (hA (v j) ((hv j).of_le (by norm_num)) x y).trans
    gcongr
    exact hgrad j
  have hd : 0 ≤ ‖x - y‖ ^ (1 - (n : ℝ) / p) := Real.rpow_nonneg (norm_nonneg _) _
  have hreal : |v j x - v j y| ≤ (A : ℝ) * (C : ℝ) *
      ‖x - y‖ ^ (1 - (n : ℝ) / p) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa only [ENNReal.ofReal_mul (mul_nonneg A.coe_nonneg C.coe_nonneg),
      ENNReal.ofReal_mul A.coe_nonneg, ENNReal.ofReal_coe_nnreal] using h
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul] using hreal
