-- Prove2me | solution 1 for GlobalTheory.RootEx.UniformLattices.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:14:32.90886+00:00
-- url     : https://prove2.me/submissions/cdc37d1b-ffa2-4ac4-a301-98b990768902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PositiveTwistAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenKerOfContinuous
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.PositiveTwistAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UniformLattices
namespace GlobalTheory.RootEx.UniformLattices
theorem _root_.solution {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have h1 : ‖(∑ k ∈ Finset.range n, z ^ k) - n‖ ≤ n / 2 := by
    have : (∑ k ∈ Finset.range n, z ^ k) - n = ∑ k ∈ Finset.range n, (z ^ k - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => (h k).le).trans ?_
    simp; linarith
  have h2 : (n : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    have := norm_sub_norm_le (n : ℂ) (∑ k ∈ Finset.range n, z ^ k)
    rw [norm_sub_rev, Complex.norm_natCast] at this
    linarith
  have h3 := h n
  rw [← geom_sum_mul, norm_mul] at h3
  rw [div_lt_iff₀ hp] at hn
  nlinarith
end GlobalTheory.RootEx.UniformLattices
