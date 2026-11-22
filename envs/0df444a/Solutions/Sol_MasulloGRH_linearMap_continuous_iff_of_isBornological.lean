-- Prove2me | solution 1 for MasulloGRH.linearMap_continuous_iff_of_isBornological
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:46:24.214802+00:00
-- url     : https://prove2.me/submissions/56a46083-40ee-4bce-8868-7c2e529dd331

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Filter Topology

theorem solution (E F : Type*)
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›) (hEb : IsBornological E)
    (hF : IsLocallyConvexTopology F ‹TopologicalSpace F›) (T : E →ₗ[ℂ] F) :
    (Continuous T ↔ SeqContinuous T) ∧
      (Continuous T ↔ ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
        Bornology.IsVonNBounded ℂ (T '' B)) := by
  obtain ⟨ι, _, p, hp⟩ := hE
  obtain ⟨κ, _, q, hq⟩ := hF
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : IsTopologicalAddGroup F := hq.topologicalAddGroup
  have : ContinuousSMul ℂ F := hq.continuousSMul
  -- a bounded linear map is continuous (bornologicity of `E`)
  have hcont : (∀ B : Set E, Bornology.IsVonNBounded ℂ B →
      Bornology.IsVonNBounded ℂ (T '' B)) → Continuous T := by
    intro hT
    refine WithSeminorms.continuous_of_continuous_comp hq T fun i => ?_
    refine hEb ((q i).comp T) fun B hB => ?_
    have h := (hq.isVonNBounded_iff_seminorm_bddAbove.mp (hT B hB)) i
    rw [Set.image_image] at h
    exact h
  -- a sequentially continuous linear map is bounded
  have hbdd : SeqContinuous T → ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
      Bornology.IsVonNBounded ℂ (T '' B) := by
    intro hT B hB
    have hε : Tendsto (fun n : ℕ => ((n : ℂ))⁻¹) atTop (𝓝 0) := by
      exact tendsto_inv_atTop_nhds_zero_nat
    refine Bornology.isVonNBounded_of_smul_tendsto_zero (ε := fun n : ℕ => ((n : ℂ))⁻¹)
      (l := atTop) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      exact inv_ne_zero this
    · intro y hy
      choose x hxB hxy using hy
      have h1 : Tendsto ((fun n : ℕ => ((n : ℂ))⁻¹) • x) atTop (𝓝 0) :=
        hB.smul_tendsto_zero (Eventually.of_forall hxB) hε
      have h2 := hT h1
      rw [map_zero] at h2
      refine h2.congr fun n => ?_
      simp [hxy n]
  refine ⟨⟨fun h => h.seqContinuous, fun h => hcont (hbdd h)⟩,
    ⟨fun h B hB => hB.image (⟨T, h⟩ : E →L[ℂ] F), hcont⟩⟩
