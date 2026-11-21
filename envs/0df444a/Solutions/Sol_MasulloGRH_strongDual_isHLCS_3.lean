-- Prove2me | solution 3 for MasulloGRH.strongDual_isHLCS
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:08:36.949044+00:00
-- url     : https://prove2.me/submissions/22f85490-8dc6-4cf7-8d5b-7a777a1ca733

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH
open scoped ComplexOrder

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) : IsHLCS (StrongDual ℂ E) := by
  obtain ⟨⟨ι, hι, p, hp⟩, hT⟩ := hE
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℝ (StrongDual ℂ E) := IsScalarTower.continuousSMul ℂ
  have : LocallyConvexSpace ℂ ℂ := by
    apply LocallyConvexSpace.ofBases ℂ ℂ (fun x => id) (fun x s => s ∈ nhds x ∧ Convex ℝ s)
    · exact fun x => LocallyConvexSpace.convex_basis (𝕜 := ℝ) x
    · intro x s hs
      exact convex_RCLike_iff_convex_real.mpr hs.2
  refine ⟨?_, inferInstance⟩
  exact ⟨{p : Seminorm ℂ (StrongDual ℂ E) // Continuous p},
    ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ (StrongDual ℂ E)⟩
