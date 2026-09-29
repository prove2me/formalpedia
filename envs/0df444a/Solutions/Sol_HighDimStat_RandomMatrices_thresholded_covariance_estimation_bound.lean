-- Prove2me | solution 1 for HighDimStat.RandomMatrices.thresholded_covariance_estimation_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:03:03.615835+00:00
-- url     : https://prove2.me/submissions/e4875f4e-7b82-4dd1-800e-2b03e18cdbf9

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm
import Definitions.Def_HighDimStat_RandomMatrices_sampleCovariance

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

/-- In dimension `0` every matrix is the zero matrix, so its operator norm vanishes. -/
lemma aux_tcov_opNorm_fin0 (M : Matrix (Fin 0) (Fin 0) ℝ) : opNorm M = 0 := by
  unfold opNorm
  rw [norm_eq_zero]
  ext v i
  exact i.elim0

/-- Numerical bound: `8 * exp (-(1/16) * 100) < 1`. -/
lemma aux_tcov_numeric : 8 * Real.exp (-((1 : ℝ) / 16) * min (100 : ℝ) (100 ^ 2)) < 1 := by
  have hmin : min (100 : ℝ) (100 ^ 2) = 100 := by norm_num
  rw [hmin]
  have h1 : Real.exp (-((1 : ℝ) / 16) * 100) ≤ Real.exp (-3) := by
    apply Real.exp_le_exp.mpr; norm_num
  have h2 : Real.exp (-3 : ℝ) < 1 / 8 := by
    have h3 : (8 : ℝ) < Real.exp 3 := by
      have he : (1 : ℝ) + 1 < Real.exp 1 := Real.add_one_lt_exp (by norm_num)
      have h4 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      rw [h4]
      have hp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      nlinarith
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos 3) (by norm_num)]
    norm_num; linarith
  linarith

end HighDimStat.RandomMatrices

open HighDimStat.RandomMatrices

theorem solution : ¬ (∀ {n d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (x : Fin n → Ω → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (hn0 : 0 < n)
    (hIndep : iIndepFun x Prob)
    (hIdent : ∀ i, IdentDistrib (x i) (x ⟨0, hn0⟩) Prob Prob)
    (hMean0 : ∀ j, ∫ ω, x ⟨0, hn0⟩ ω j ∂Prob = 0)
    (hCov : ∀ j k, ∫ ω, x ⟨0, hn0⟩ ω j * x ⟨0, hn0⟩ ω k ∂Prob = Sig j k)
    (hSubG : ∀ j, ∀ lam' : ℝ, Integrable (fun ω => Real.exp (lam' * x ⟨0, hn0⟩ ω j)) Prob ∧
      ∫ ω, Real.exp (lam' * x ⟨0, hn0⟩ ω j) ∂Prob ≤ Real.exp (σ ^ 2 * lam' ^ 2 / 2))
    (hnd : Real.log d < n)
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ)
    (hlam : lam / σ ^ 2 = 8 * Real.sqrt (Real.log d / n) + δ),
    Prob.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * Real.exp (-((n : ℝ) / 16) * min δ (δ ^ 2))) := by
  intro h
  have key := @h 1 0 Unit _ (Measure.dirac ()) _ (fun _ _ => Fin.elim0) 0 1 Nat.one_pos
    iIndepFun.of_subsingleton
    (fun _ => IdentDistrib.refl measurable_const.aemeasurable)
    (fun j => j.elim0) (fun j => j.elim0) (fun j => j.elim0)
    (by simp) 100 (by norm_num) 100 (by simp)
  simp only [aux_tcov_opNorm_fin0, mul_zero, zero_mul, le_refl, Set.ofPred_true, probReal_univ,
    Nat.cast_one] at key
  linarith [aux_tcov_numeric]
