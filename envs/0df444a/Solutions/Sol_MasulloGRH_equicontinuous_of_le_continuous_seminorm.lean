-- Prove2me | solution 1 for MasulloGRH.equicontinuous_of_le_continuous_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:16:35.493525+00:00
-- url     : https://prove2.me/submissions/e1c3ee99-75d1-4bb7-a1ef-b71d73c9a114

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter

theorem solution (F : Type*) [AddCommGroup F] [Module ℂ F]
    [TopologicalSpace F] (hF : IsLocallyConvexTopology F ‹TopologicalSpace F›)
    (r : Seminorm ℂ F) (hr : Continuous r) (ψ : ℕ → F →ₗ[ℂ] ℂ) (hψ : ∀ m y, ‖ψ m y‖ ≤ r y) :
    ∃ ψ' : ℕ → StrongDual ℂ F, (∀ m y, ψ' m y = ψ m y) ∧
      Equicontinuous (fun m => (ψ' m : F → ℂ)) := by
  obtain ⟨ι, hι, p, hp⟩ := hF
  have : PolynormableSpace ℂ F := hp.toPolynormableSpace
  have : IsTopologicalAddGroup F := hp.topologicalAddGroup
  have : ContinuousSMul ℂ F := hp.continuousSMul
  let _ : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have hcont (m : ℕ) : Continuous (ψ m) :=
    (PolynormableSpace.withSeminorms ℂ F).continuous_normedSpace_rng ℂ (ψ m)
      ⟨{⟨r, hr⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp (ψ m) ≤ r from hψ m)⟩
  refine ⟨fun m => ⟨ψ m, hcont m⟩, fun _ _ => rfl, ?_⟩
  exact ((norm_withSeminorms ℂ ℂ).uniformEquicontinuous_iff_exists_continuous_seminorm ψ).mpr
    (fun _ => ⟨r, hr, hψ⟩) |>.equicontinuous
