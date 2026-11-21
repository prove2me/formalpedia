-- Prove2me | solution 1 for MasulloGRH.strongDual_isHLCS
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:07:04.208763+00:00
-- url     : https://prove2.me/submissions/2af362d4-b8d2-4b5e-9544-d9a66f1eec69

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH
open scoped ComplexOrder

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) :
    IsHLCS (StrongDual ℂ E) := by
  obtain ⟨⟨ι, _, p, hp⟩, _⟩ := hE
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  have : ContinuousSMul ℝ (StrongDual ℂ E) := by
    refine ⟨?_⟩
    have h : Continuous (fun q : ℝ × StrongDual ℂ E => ((q.1 : ℂ)) • q.2) :=
      (Complex.continuous_ofReal.comp continuous_fst).smul continuous_snd
    refine h.congr fun q => ?_
    exact (Complex.coe_smul q.1 q.2)
  have : LocallyConvexSpace ℂ ℂ :=
    LocallyConvexSpace.ofBasisZero ℂ ℂ _ _ (Metric.nhds_basis_ball (x := (0 : ℂ)))
      (fun r _ => convex_of_nonneg_surjective_algebraMap _
        (fun z hz => by
          obtain ⟨x, hx, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp (Set.mem_Ici.mp hz)
          exact ⟨x, hx, rfl⟩) (convex_ball (0 : ℂ) r))
  exact ⟨⟨AbsConvexOpenSets ℂ (StrongDual ℂ E), inferInstance,
    gaugeSeminormFamily ℂ (StrongDual ℂ E), with_gaugeSeminormFamily⟩, inferInstance⟩
