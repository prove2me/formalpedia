-- Prove2me | solution 1 for LocallyConvexDuality.induced_pointwise_eq_induced_precompact_of_equicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:16:01.640457+00:00
-- url     : https://prove2.me/submissions/f1324f01-0f50-476a-970b-62a8e87faae0

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

theorem solution {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F]
    (H : Set (E →L[𝕜] F))
    (hH : Equicontinuous (fun f : H => ((f : E →L[𝕜] F) : E → F))) :
    TopologicalSpace.induced
        (fun f : H => UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F {S : Set E | S.Finite}
          (f : E →L[𝕜] F))
        inferInstance =
      TopologicalSpace.induced
        (fun f : H => UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F {S : Set E | TotallyBounded S}
          (f : E →L[𝕜] F))
        inferInstance := by
  -- For linear maps, equicontinuity (at `0`) upgrades to uniform equicontinuity.
  have hu : UniformEquicontinuous (fun f : H => ((f : E →L[𝕜] F) : E → F)) :=
    uniformEquicontinuous_of_equicontinuousAt_zero (fun f : H => (f : E →L[𝕜] F)) (hH 0)
  -- Two topologies agree as soon as they have the same convergent filters.
  refine TopologicalSpace.ext_nhds fun f => eq_of_forall_le_iff fun l => ?_
  rw [nhds_induced, nhds_induced, ← Filter.tendsto_iff_comap, ← Filter.tendsto_iff_comap,
    UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn,
    UniformConvergenceCLM.tendsto_iff_tendstoUniformlyOn]
  constructor
  · -- pointwise convergence ⟹ uniform convergence on totally bounded sets
    intro h s hs U hU
    have hs' : TotallyBounded s := hs
    obtain ⟨V, hV, hVsymm, hVU⟩ := comp_comp_symm_mem_uniformity_sets hU
    obtain ⟨W, hW, hWV⟩ :=
      (uniformity E).basis_sets.uniformEquicontinuous_iff_left.mp hu V hV
    -- a finite `W`-net `t` of `s`
    obtain ⟨t, ht, hcover⟩ := hs' W hW
    -- pointwise convergence controls all the centres of the net at once
    have htend : ∀ᶠ g : H in l, ∀ y ∈ t, ((f : E →L[𝕜] F) y, (g : E →L[𝕜] F) y) ∈ V := by
      refine (Filter.eventually_all_finite ht).mpr fun y _ => ?_
      have hy := h {y} (Set.finite_singleton y) V hV
      filter_upwards [hy] with g hg
      exact hg y (Set.mem_singleton y)
    filter_upwards [htend] with g hg x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hx)
    have h1 : ((f : E →L[𝕜] F) x, (f : E →L[𝕜] F) y) ∈ V := hWV x y hxy f
    have h2 : ((f : E →L[𝕜] F) y, (g : E →L[𝕜] F) y) ∈ V := hg y hy
    have h3 : ((g : E →L[𝕜] F) x, (g : E →L[𝕜] F) y) ∈ V := hWV x y hxy g
    have h3' : ((g : E →L[𝕜] F) y, (g : E →L[𝕜] F) x) ∈ V := SetRel.symm V h3
    exact hVU (SetRel.prodMk_mem_comp (SetRel.prodMk_mem_comp h1 h2) h3')
  · -- finite sets are totally bounded
    intro h s hs
    exact h s (Set.Finite.totallyBounded hs)
