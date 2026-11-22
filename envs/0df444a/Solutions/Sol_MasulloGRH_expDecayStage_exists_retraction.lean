-- Prove2me | solution 1 for MasulloGRH.expDecayStage_exists_retraction
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:57:51.145304+00:00
-- url     : https://prove2.me/submissions/0f9fa3fd-e1a2-43e9-9481-c7c3f70ed484

import Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_average
import Theorems.Thm_MasulloGRH_expDecayStage_frechet_nuclear

set_option autoImplicit false

universe u

open MasulloGRH in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    ∃ P : ExpDecaySchwartz G m I →ₗ[ℂ] ExpDecayStage G m I k, Continuous P ∧
      ∀ y, P (ExpDecayStage.incl G m I k y) = y := by
  obtain ⟨A, hAr, hAc⟩ := expDecaySchwartz_exists_average G m hm I hI hne k hk
  refine ⟨A, ?_, hAr⟩
  obtain ⟨⟨ι, hι, p, hp⟩, -⟩ := (expDecayStage_frechet_nuclear G m hm I hI hne k hk).1
  rw [continuous_iff_le_induced]
  refine sInf_le ⟨⟨ι, hι, p.comp A, LinearMap.withSeminorms_induced hp A⟩, fun k' hk' => ?_⟩
  exact continuous_induced_rng.2 (hAc k' hk')
