-- Prove2me | solution 1 for LocallyConvexDuality.barrelledSpace_iff_barrel_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:00:36.227272+00:00
-- url     : https://prove2.me/submissions/f3cd58a0-63c7-47b6-b0e3-d529afc64add

import Mathlib

open scoped Topology ComplexOrder

set_option autoImplicit false

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] :
    BarrelledSpace 𝕜 E ↔
      ∀ D : Set E, IsClosed D → AbsConvex 𝕜 D → Absorbent 𝕜 D → D ∈ 𝓝 (0 : E) := by
  -- the underlying real vector space structure of `E`
  let : Module ℝ E := Module.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  constructor
  · -- every lower semicontinuous seminorm is continuous ⟹ every barrel is a neighbourhood of `0`
    intro h D hClosed hAbsConvex hAbsorbent
    have hConvexReal : Convex ℝ D := convex_RCLike_iff_convex_real.mp hAbsConvex.2
    have hAbsorbentReal : Absorbent ℝ D := by
      intro x
      refine (hAbsorbent x).restrict_scalars ?_
      have hiso : Isometry (fun r : ℝ ↦ (r • (1 : 𝕜))) := by
        refine Isometry.of_dist_eq fun a b ↦ ?_
        rw [dist_eq_norm, ← sub_smul, norm_smul, norm_one, mul_one, ← dist_eq_norm]
      exact hiso.antilipschitz.tendsto_cobounded
    have hzero : (0 : E) ∈ D := hAbsorbentReal.zero_mem
    -- the gauge of the barrel is a seminorm
    let p : Seminorm 𝕜 E := gaugeSeminorm hAbsConvex.1 hConvexReal hAbsorbentReal
    -- its sublevel sets `{gauge ≤ r}` are intersections of closed dilates `t • D`, `t > r ≥ 0`
    have hp : LowerSemicontinuous p := by
      rw [lowerSemicontinuous_iff_isClosed_preimage]
      intro r
      change IsClosed {x : E | gauge D x ≤ r}
      by_cases hr : 0 ≤ r
      · rw [setOfPred_gauge_le_eq hConvexReal hzero hAbsorbentReal hr]
        exact isClosed_iInter fun t ↦ isClosed_iInter fun ht ↦
          hClosed.smul_of_ne_zero (hr.trans_lt ht).ne'
      · rw [show {x : E | gauge D x ≤ r} = ∅ from
          Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ hr ((gauge_nonneg x).trans hx)]
        exact isClosed_empty
    -- hence the gauge is continuous and its open unit ball, contained in `D`, is a neighbourhood
    have hcont : Continuous p := p.continuous_of_lowerSemicontinuous hp
    refine Filter.mem_of_superset ((Seminorm.continuous_iff (p := p) one_pos).mp hcont) ?_
    rw [p.ball_zero_eq]
    exact setOfPred_gauge_lt_one_subset_self hConvexReal hzero hAbsorbentReal
  · -- every barrel is a neighbourhood of `0` ⟹ every lower semicontinuous seminorm is continuous
    intro h
    refine ⟨fun p hp ↦ Seminorm.continuous' (r := 1) (h (p.closedBall 0 1) ?_ ?_ ?_)⟩
    · rw [p.closedBall_zero_eq]
      exact hp.isClosed_preimage 1
    · exact ⟨p.balanced_closedBall_zero 1,
        convex_RCLike_iff_convex_real.mpr (p.convex_closedBall 0 1)⟩
    · exact p.absorbent_closedBall_zero one_pos
