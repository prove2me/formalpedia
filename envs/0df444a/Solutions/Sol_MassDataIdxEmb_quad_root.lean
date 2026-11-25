-- Prove2me | solution 1 for MassDataIdxEmb.quad_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:28.023985+00:00
-- url     : https://prove2.me/submissions/bdb2cc46-ea6d-4716-a452-d8cafe39fac7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_QuadRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxEmb
open Metric
namespace MassDataIdxEmb
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c0 c1 : K) (h1 : ‖c1‖ = 1) (h0 : ‖c0‖ < 1) :
    ∃ x : K, x * x + c1 * x + c0 = 0 := by
  have hnorm : ∀ x : K, ‖x‖ ≤ ‖c0‖ → ‖c1 + x‖ = 1 := by
    intro x hx
    have hne : ‖c1‖ ≠ ‖x‖ := by rw [h1]; exact (lt_of_le_of_lt hx h0).ne'
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, h1]
    exact max_eq_left (hx.trans h0.le)
  have hne0 : ∀ x : K, ‖x‖ ≤ ‖c0‖ → c1 + x ≠ 0 := fun x hx h => by
    have h' := hnorm x hx
    rw [h, norm_zero] at h'
    exact zero_ne_one h'
  set f : K → K := fun x => -c0 / (c1 + x) with hf
  have hmaps : Set.MapsTo f (closedBall 0 ‖c0‖) (closedBall 0 ‖c0‖) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    simp only [hf, norm_div, norm_neg, hnorm x hx, div_one, le_refl]
  haveI : IsClosed (closedBall (0 : K) ‖c0‖) := isClosed_closedBall
  haveI : CompleteSpace (closedBall (0 : K) ‖c0‖) := IsClosed.completeSpace_coe
  haveI : Nonempty (closedBall (0 : K) ‖c0‖) := ⟨⟨0, mem_closedBall_self (norm_nonneg _)⟩⟩
  have hcon : ContractingWith ⟨‖c0‖, norm_nonneg _⟩ (hmaps.restrict f _ _) := by
    refine ⟨NNReal.coe_lt_coe.1 (by rw [NNReal.coe_one]; exact h0),
      LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    have ha := mem_closedBall_zero_iff.1 a.2
    have hb := mem_closedBall_zero_iff.1 b.2
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    show ‖f a - f b‖ ≤ ‖c0‖ * ‖(a : K) - b‖
    have he : f a - f b = c0 * ((a : K) - b) / ((c1 + a) * (c1 + b)) := by
      simp only [hf]
      field_simp [hne0 _ ha, hne0 _ hb]
      ring
    rw [he, norm_div, norm_mul, norm_mul, hnorm _ ha, hnorm _ hb, mul_one, div_one]
  obtain ⟨x0, hx0e⟩ : ∃ x0 : closedBall (0 : K) ‖c0‖, hmaps.restrict f _ _ x0 = x0 :=
    ⟨_, hcon.fixedPoint_isFixedPt⟩
  have hfix : f (x0 : K) = x0 := congrArg Subtype.val hx0e
  refine ⟨(x0 : K), ?_⟩
  have hx0 := hne0 _ (mem_closedBall_zero_iff.1 x0.2)
  simp only [hf] at hfix
  rw [div_eq_iff hx0] at hfix
  linear_combination -hfix
end MassDataIdxEmb
