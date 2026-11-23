-- Prove2me | solution 1 for KernelRank.separableRank_radial_sq_mul_cos_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:50:30.336536+00:00
-- url     : https://prove2.me/submissions/500718f0-9944-4174-9296-8393c02306ba

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
import Theorems.Thm_KernelRank_separableRank_radial_complex_eq_iff
import Theorems.Thm_KernelRank_IsSumOfProducts_comp
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_fin2Vec_one
import Theorems.Thm_KernelRank_fin2Vec_zero
import Theorems.Thm_KernelRank_singleCoeff_same
attribute [local simp] KernelRank.expPoly_zero
attribute [local simp] KernelRank.fin2Vec_one
attribute [local simp] KernelRank.fin2Vec_zero
attribute [local simp] KernelRank.singleCoeff_same



set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank
namespace KernelRank
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) :
    separableRank (fun x : Fin d → ℝ =>
      (((∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2) : ℝ) : ℂ)) = (2 * d : ℕ) := by
  classical
  let S : Finset ℂ := {I, -I}
  let P : ℂ → ℂ[X] := fun _ => Polynomial.C (1 / 2 : ℂ) * Polynomial.X
  have hneI : (I : ℂ) ≠ -I := by
    intro h
    have : (1 : ℝ) = -1 := by simpa using congrArg Complex.im h
    linarith
  have hP0 : ∀ μ ∈ S, P μ ≠ 0 := fun _ _ => by simp [P]
  have hdeg : ∀ μ, (P μ).natDegree = 1 := fun _ => by
    rw [Polynomial.natDegree_C_mul (by norm_num : (1 / 2 : ℂ) ≠ 0), Polynomial.natDegree_X]
  have hcont : ContinuousOn
      (fun s : ℝ => (((s * Real.cos s : ℝ) : ℂ))) (Set.Ici 0) :=
    (Complex.continuous_ofReal.comp (continuous_id.mul Real.continuous_cos)).continuousOn
  rw [separableRank_radial_complex_eq_iff hd _ hcont (2 * d)]
  refine ⟨S, P, hP0, ?_, ?_⟩
  · intro s _hs
    simp only [S, Finset.sum_pair hneI, expPoly, P, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Complex.ofReal_mul, Complex.ofReal_cos]
    rw [Complex.cos]
    have h1 : (s : ℂ) * I = I * (s : ℂ) := mul_comm _ _
    have h2 : -(s : ℂ) * I = -I * (s : ℂ) := by ring
    rw [h1, h2]
    ring
  · simp [S, Finset.sum_pair hneI, hdeg]
    omega
end KernelRank
