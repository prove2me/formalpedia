-- Prove2me | solution 1 for GlobalTheory.norm_det_one_add_sub_one_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:31.677363+00:00
-- url     : https://prove2.me/submissions/5bba85db-6aaf-427e-a942-990cccea9e39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
import Theorems.Thm_GlobalTheory_norm_multisetProd_sub_one_le_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hM : ∀ a b, ‖M a b‖ ≤ ε) :
    ‖(1 + M).det - 1‖ ≤ Real.exp (Fintype.card n * (Fintype.card n * ε)) - 1 := by
  have hs : ∀ μ ∈ (1 + M).charpoly.roots, ‖μ - 1‖ ≤ Fintype.card n * ε := by
    intro μ hμ
    have h1 : μ ∈ spectrum ℂ (1 + M) :=
      mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : μ - 1 ∈ spectrum ℂ M := by
      rw [spectrum.mem_iff] at h1 ⊢
      convert h1 using 2
      rw [map_sub, map_one]
      abel
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at h2
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball h2
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have h3 := Finset.add_sum_erase Finset.univ (fun j => ‖M k j‖) (Finset.mem_univ k)
    have h4 : ∑ j, ‖M k j‖ ≤ Fintype.card n * ε := by
      simpa using Finset.sum_le_card_nsmul Finset.univ (fun j => ‖M k j‖) ε fun j _ => hM k j
    have h5 := norm_le_insert' (μ - 1) (M k k)
    linarith
  have hc : (1 + M).charpoly.roots.card = Fintype.card n := by
    rw [← charpoly_natDegree_eq_dim (1 + M)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have h := norm_multisetProd_sub_one_le_exp _ (by positivity) hs
  rwa [← det_eq_prod_roots_charpoly, hc] at h
end GlobalTheory
