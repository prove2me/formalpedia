-- Prove2me | solution 1 for LocallyConvexDuality.isVonNBounded_uniformConvergenceCLM_of_equicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:05:37.436271+00:00
-- url     : https://prove2.me/submissions/1884c679-b7e6-48c3-94e8-d248bd02afa2

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

/-- An equicontinuous set `H` of continuous linear maps `E → F` is bounded for the topology of
uniform convergence on the members of any family `𝔖` of bounded subsets of `E`. -/
theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S)
    (H : Set (E →L[𝕜] F))
    (hH : Equicontinuous (fun f : H => ((f : E →L[𝕜] F) : E → F))) :
    Bornology.IsVonNBounded 𝕜 (UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F 𝔖 '' H) := by
  -- Boundedness in `E →Lᵤ[𝕜, 𝔖] F` means: `H(T)` is bounded in `F` for every `T ∈ 𝔖`.
  rw [UniformConvergenceCLM.isVonNBounded_iff]
  intro T hT V hV
  -- The entourage of `F` attached to the `0`-neighbourhood `V`.
  have hVu : {p : F × F | p.2 - p.1 ∈ V} ∈ uniformity F := by
    rw [uniformity_eq_comap_nhds_zero F]
    exact Filter.preimage_mem_comap hV
  -- Equicontinuity at `0`: a single `0`-neighbourhood of `E` is mapped into `V` by all `f ∈ H`.
  have h0 : {x : E | ∀ f : H, (f : E →L[𝕜] F) x ∈ V} ∈ nhds (0 : E) := by
    filter_upwards [hH 0 _ hVu] with x hx f
    have h := hx f
    simp only [map_zero, sub_zero] at h
    exact h
  -- `T` is absorbed by that neighbourhood; the same scalars make `V` absorb `H(T)`.
  filter_upwards [h𝔖 T hT h0] with a ha
  rintro _ ⟨_, ⟨f, hf, rfl⟩, x, hx, rfl⟩
  obtain ⟨u, hu, rfl⟩ := ha hx
  exact ⟨f u, hu ⟨f, hf⟩, (map_smul f a u).symm⟩
