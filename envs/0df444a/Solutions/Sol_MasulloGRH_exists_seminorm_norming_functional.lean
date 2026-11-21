-- Prove2me | solution 1 for MasulloGRH.exists_seminorm_norming_functional
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:30:58.124181+00:00
-- url     : https://prove2.me/submissions/4c40d03e-ec02-40d4-8a25-49b77a044191

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology
noncomputable section

private theorem seminorm_norming {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : Seminorm ℂ E) (x : E) :
    ∃ f : E →ₗ[ℂ] ℂ, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by
  let _ : SeminormedAddCommGroup E := p.toSeminormedAddCommGroup
  let _ : NormedSpace ℂ E := { norm_smul_le := fun a b => (map_smul_eq_mul p a b).le }
  obtain ⟨f, hf, hx⟩ := exists_dual_vector'' ℂ x
  refine ⟨f.toLinearMap, fun y => ?_, ?_⟩
  · change ‖f y‖ ≤ ‖y‖
    exact (f.le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg y))
  · change ‖f x‖ = ‖x‖
    rw [hx]
    simp only [RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg x)]

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›)
    (p : Seminorm ℂ E) (hp : Continuous p) (x : E) :
    ∃ f : StrongDual ℂ E, (∀ y, ‖f y‖ ≤ p y) ∧ ‖f x‖ = p x := by
  obtain ⟨ι, hι, ps, hps⟩ := hE
  have : PolynormableSpace ℂ E := hps.toPolynormableSpace
  obtain ⟨f, hf, hx⟩ := seminorm_norming p x
  have hc : Continuous f := (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng ℂ f
    ⟨{⟨p, hp⟩}, 1, by simpa using (show (normSeminorm ℂ ℂ).comp f ≤ p from hf)⟩
  exact ⟨⟨f, hc⟩, hf, hx⟩

