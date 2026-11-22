-- Prove2me | solution 1 for LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_of_orthogonalFamily
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:45:25.020368+00:00
-- url     : https://prove2.me/submissions/5a33de60-2f08-4e72-913f-3c6525278376

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} [Finite ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)]
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    IsClosed ((⨆ i, V i : Submodule 𝕜 E) : Set E) := by
  classical
  let := Fintype.ofFinite ι
  have hset : ((⨆ i, V i : Submodule 𝕜 E) : Set E) =
      {x : E | (∑ i, (V i).starProjection x) = x} := by
    ext x
    constructor
    · exact hV.sum_projection_of_mem_iSup x
    · intro hx
      change (∑ i, (V i).starProjection x) = x at hx
      rw [← hx]
      exact Submodule.sum_mem _ fun i _ =>
        (le_iSup V i) ((V i).starProjection_apply_mem x)
  rw [hset]
  exact isClosed_eq (continuous_finsetSum _ fun i _ => (V i).starProjection.continuous)
    continuous_id

#print axioms solution
