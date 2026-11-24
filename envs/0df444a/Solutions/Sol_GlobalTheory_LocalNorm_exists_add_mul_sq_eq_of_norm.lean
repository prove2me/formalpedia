-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_add_mul_sq_eq_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:02.27146+00:00
-- url     : https://prove2.me/submissions/e2365f70-2876-4979-ac29-21084bf55cd1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
namespace GlobalTheory.LocalNorm
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] {c e : K} (hc : ‖c‖ ≤ 1) (he : ‖e‖ < 1) : ∃ t, t + c * t ^ 2 = e := by
  have hsf : Set.MapsTo (fun t : K => e - c * t ^ 2) (Metric.closedBall 0 ‖e‖)
      (Metric.closedBall 0 ‖e‖) := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht ⊢
    beta_reduce
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h0 := norm_nonneg t
    have h1 : ‖t‖ ^ 2 ≤ ‖e‖ := by nlinarith
    nlinarith [norm_nonneg c, sq_nonneg ‖t‖]
  have hcon : ContractingWith ‖e‖₊ (hsf.restrict _ _ _) := by
    refine ⟨by exact_mod_cast he, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hx := mem_closedBall_zero_iff.1 x.2
    have hy := mem_closedBall_zero_iff.1 y.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simp only [Set.MapsTo.val_restrict_apply, coe_nnnorm]
    have h1 : e - c * (x : K) ^ 2 - (e - c * (y : K) ^ 2)
        = -(c * ((x : K) + y) * ((x : K) - y)) := by ring
    have h2 : ‖(x : K) + y‖ ≤ ‖e‖ := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    rw [h1, norm_neg, norm_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    nlinarith [norm_nonneg c, norm_nonneg ((x : K) + y)]
  obtain ⟨t, -, ht, -⟩ := hcon.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hsf
    (x := 0) (Metric.mem_closedBall_self (norm_nonneg e)) (edist_ne_top _ _)
  have ht' : e - c * t ^ 2 = t := ht
  exact ⟨t, by linear_combination -ht'⟩
end GlobalTheory.LocalNorm
