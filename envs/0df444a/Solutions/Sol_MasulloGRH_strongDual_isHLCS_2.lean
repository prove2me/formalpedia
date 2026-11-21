-- Prove2me | solution 2 for MasulloGRH.strongDual_isHLCS
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:08:14.483201+00:00
-- url     : https://prove2.me/submissions/d05cde62-fbc9-4654-895f-c7215117473f

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH
open scoped ComplexOrder

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) :
    IsHLCS (StrongDual ℂ E) := by
  obtain ⟨⟨ι, _, p, hp⟩, _⟩ := hE
  have hadd : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := hp.continuousSMul
  have hT2 : T2Space (StrongDual ℂ E) := inferInstance
  have hsR : ContinuousSMul ℝ (StrongDual ℂ E) :=
    IsScalarTower.continuousSMul (M := ℝ) (α := StrongDual ℂ E) ℂ
  have hlcR : LocallyConvexSpace ℝ (StrongDual ℂ E) := inferInstance
  have hlc : LocallyConvexSpace ℂ (StrongDual ℂ E) := by
    rw [locallyConvexSpace_iff_exists_convex_subset_zero]
    intro U hU
    obtain ⟨S, hS, hSc, hSU⟩ :=
      (locallyConvexSpace_iff_exists_convex_subset_zero ℝ (StrongDual ℂ E)).1 hlcR U hU
    exact ⟨S, hS, convex_RCLike_iff_convex_real.mpr hSc, hSU⟩
  exact ⟨⟨AbsConvexOpenSets ℂ (StrongDual ℂ E), inferInstance,
    gaugeSeminormFamily ℂ (StrongDual ℂ E), with_gaugeSeminormFamily⟩, hT2⟩
