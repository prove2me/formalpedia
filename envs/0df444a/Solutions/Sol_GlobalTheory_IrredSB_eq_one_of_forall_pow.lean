-- Prove2me | solution 1 for GlobalTheory.IrredSB.eq_one_of_forall_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:58.815953+00:00
-- url     : https://prove2.me/submissions/9b8577c1-5dab-437f-8fc7-d010e59dddf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.IrredSB
namespace GlobalTheory.IrredSB
theorem _root_.solution {z : ℂ} (hz : ‖z‖ = 1) (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1) : z = 1 := by
  by_contra hne
  have hb : ∀ n : ℕ, (n : ℝ) / 2 ≤ (∑ k ∈ Finset.range n, z ^ k).re := by
    intro n
    rw [Complex.re_sum]
    have hk : ∀ k ∈ Finset.range n, (1 / 2 : ℝ) ≤ (z ^ k).re := by
      intro k _
      have h1 : ‖z ^ k‖ ^ 2 = 1 := by rw [norm_pow, hz, one_pow, one_pow]
      have h2 : ‖z ^ k - 1‖ ^ 2 < 1 := by nlinarith [h k, norm_nonneg (z ^ k - 1)]
      rw [Complex.sq_norm, Complex.normSq_apply] at h1 h2
      simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero] at h2
      nlinarith
    have := Finset.card_nsmul_le_sum _ _ _ hk
    rw [Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  have h3 : (∑ k ∈ Finset.range n, z ^ k).re ≤ 1 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [geom_sum_eq hne, norm_div]
    exact div_le_div_of_nonneg_right (h n).le hp.le
  have h4 := hb n
  have h5 : 2 / ‖z - 1‖ = 2 * (1 / ‖z - 1‖) := by ring
  linarith
end GlobalTheory.IrredSB
