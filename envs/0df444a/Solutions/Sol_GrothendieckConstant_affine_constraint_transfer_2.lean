-- Prove2me | solution 2 for GrothendieckConstant.affine_constraint_transfer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T14:58:05.821942+00:00
-- url     : https://prove2.me/submissions/2d200075-7f44-4158-b8ea-a2fd1d9935e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_sign_pair_affine_constraint_of_krivine
import Theorems.Thm_GrothendieckLB_mixed_avgCorr_coefficients
import Theorems.Thm_GrothendieckLB_majorant_barrier
import Theorems.Thm_GrothendieckLB_lemma_10_2

open Filter Topology MeasureTheory GrothendieckConstant GrothendieckLB

/- An affine inequality survives a probability average because the integral
of its constant term is the same constant. -/
private theorem mixed_coeff_bounds (lam : ℝ)
    (hcon : ∀ (k : ℕ) (S : KrivineScheme k),
      (1 + lam) * coeffLinear S - (lam + 5 / 6) ≤ coeffCubic S)
    {d : ℕ} (S : MixedScheme d) :
    (1 + lam) * taylorCoeff 1 S.avgCorr - (lam + 5 / 6) ≤ taylorCoeff 3 S.avgCorr ∧
      taylorCoeff 1 S.avgCorr ≤ 1 := by
  let _ := S.mΩ
  let _ := S.prob
  obtain ⟨h₁, h₃, hi₁, hi₃, hmass⟩ := mixed_avgCorr_coefficients S
  refine ⟨?_, hmass⟩
  rw [h₁, h₃]
  have hi := (hi₁.const_mul (1 + lam)).sub (integrable_const (lam + 5 / 6))
  have havg := integral_mono hi hi₃ (fun ω =>
    sign_pair_affine_constraint_of_krivine lam hcon (S.sign_F ω) (S.sign_G ω))
  simpa only [Pi.sub_apply, integral_sub (hi₁.const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul] using havg

/- Apply the barrier to every term of the optimality sequence, then take the
limit of its costs π / (2γₙ). -/
theorem solution (lam : ℝ) (hlam : 1 / 2 ≤ lam)
    (hcon : ∀ (k : ℕ) (S : KrivineScheme k),
      (1 + lam) * coeffLinear S - (lam + 5 / 6) ≤ coeffCubic S) :
    Real.pi * (1 + lam) / (2 * (lam + 5 / 6)) ≤ grothendieckConst := by
  have hslope : 0 < 1 + lam := by linarith
  have hintercept : 0 < lam + 5 / 6 := by linarith
  obtain ⟨H, γ, hseq, _, hcost⟩ := lemma_10_2
  apply ge_of_tendsto' hcost
  intro n
  obtain ⟨hodd, han, ⟨d, S, hcoeff⟩, hadm, _⟩ := hseq n
  have hmixed := fun j => mixed_coeff_bounds lam hcon (S j)
  have hstrip := le_of_tendsto_of_tendsto'
    (((hcoeff 1).const_mul (1 + lam)).sub_const (lam + 5 / 6))
    (hcoeff 3) (fun j => (hmixed j).1)
  have hmass := le_of_tendsto' (hcoeff 1) (fun j => (hmixed j).2)
  have hlinear : 0 < taylorCoeff 1 (H n) := by
    simpa [taylorCoeff] using hadm.2.2.1
  have hcap := majorant_barrier lam hlam hodd han hlinear hmass hstrip hadm
  have hγ : 0 < γ n := hadm.2.2.2.1
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith only [mul_le_mul_of_nonneg_left ((le_div_iff₀ hslope).mp hcap) Real.pi_pos.le]
