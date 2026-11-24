-- Prove2me | solution 1 for GlobalTheory.CuspRep.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:36:17.378994+00:00
-- url     : https://prove2.me/submissions/f548f145-6109-4afb-a4ef-77a1341ff401

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsOpenKerFinIdele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CuspRep
namespace GlobalTheory.CuspRep
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
end GlobalTheory.CuspRep
