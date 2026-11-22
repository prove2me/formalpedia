-- Prove2me | solution 1 for MasulloGRH.indTensor_eq_projTensor_of_isFrechet
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:16:23.244011+00:00
-- url     : https://prove2.me/submissions/38699c5b-5e19-4f33-abce-093fad19d3f2

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_indTensor_isHLCS
import Theorems.Thm_MasulloGRH_indTensor_le_projTensor_le_epsTensor
import Theorems.Thm_SeparateContinuity_seqContinuous_of_separately_seqContinuous

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

namespace Sol_MasulloGRH_indTensor_eq_projTensor_of_isFrechet

open MasulloGRH Uniformity

/-- A metrizable topological vector space which is complete in the sense of `IsCompleteTVS`
(every Cauchy filter for the additive uniform structure converges) is completely metrizable. -/
theorem isCompletelyMetrizableSpace_of_isCompleteTVS {E : Type u} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [TopologicalSpace.MetrizableSpace E]
    (hc : IsCompleteTVS E) : TopologicalSpace.IsCompletelyMetrizableSpace E := by
  -- the additive uniform structure of `E`
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : T2Space E := hc.1
  -- its uniformity is countably generated because `0` has a countable neighbourhood base
  have : (𝓤 E).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  -- it is complete: a Cauchy filter of the uniform structure is Cauchy in the sense of the
  -- definition `IsCauchyFilter`
  have : CompleteSpace E := by
    refine ⟨fun {f} hf => ?_⟩
    refine hc.2 f ⟨hf.1, fun U hU => ?_⟩
    have h2 : (fun p : E × E => p.2 + -p.1) ⁻¹' U ∈ 𝓤 E := by
      rw [uniformity_eq_comap_nhds_zero' E]
      exact preimage_mem_comap hU
    obtain ⟨A, hA, hAU⟩ := (cauchy_iff.1 hf).2 _ h2
    refine ⟨A, hA, fun x hx y hy => ?_⟩
    have h3 : x + -y ∈ U := hAU (Set.mk_mem_prod hy hx)
    rwa [← sub_eq_add_neg] at h3
  infer_instance

end Sol_MasulloGRH_indTensor_eq_projTensor_of_isFrechet

open MasulloGRH Sol_MasulloGRH_indTensor_eq_projTensor_of_isFrechet in
theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsFrechet E) (hF : IsFrechet F) :
    indTensorTopology E F = projTensorTopology E F := by
  -- Fréchet spaces are Hausdorff locally convex
  have hE' : IsHLCS E := ⟨hE.1, hE.2.1.1⟩
  have hF' : IsHLCS F := ⟨hF.1, hF.2.1.1⟩
  -- `ι ≤ π` always; it remains to show `π ≤ ι`
  refine le_antisymm (indTensor_le_projTensor_le_epsTensor E F hE' hF').1 ?_
  -- `E` and `F` are topological vector spaces; `E` is completely metrizable, `F` is metrizable
  obtain ⟨ιE, _, pE, hpE⟩ := hE.1
  obtain ⟨ιF, _, pF, hpF⟩ := hF.1
  have : IsTopologicalAddGroup E := hpE.topologicalAddGroup
  have : ContinuousSMul ℂ E := hpE.continuousSMul
  have : IsTopologicalAddGroup F := hpF.topologicalAddGroup
  have : ContinuousSMul ℂ F := hpF.continuousSMul
  have : TopologicalSpace.MetrizableSpace E := hE.2.2
  have : TopologicalSpace.MetrizableSpace F := hF.2.2
  have : TopologicalSpace.IsCompletelyMetrizableSpace E :=
    isCompletelyMetrizableSpace_of_isCompleteTVS hE.2.1
  -- the inductive topology is locally convex, so `E ⊗_ι F` is a topological vector space
  obtain ⟨ι, hι, p, hp⟩ := (indTensor_isHLCS E F hE' hF').1
  -- it suffices to show that `⊗ : E × F → E ⊗_ι F` is (jointly) continuous
  refine sInf_le ⟨⟨ι, hι, p, hp⟩, ?_⟩
  let : TopologicalSpace (E ⊗[ℂ] F) := indTensorTopology E F
  have : IsTopologicalAddGroup (E ⊗[ℂ] F) := hp.topologicalAddGroup
  have : ContinuousSMul ℂ (E ⊗[ℂ] F) := hp.continuousSMul
  -- `⊗` is separately continuous into `E ⊗_ι F`, by the definition of the inductive topology
  have h1 : ∀ x : E, Continuous (fun y : F => x ⊗ₜ[ℂ] y) := fun x =>
    continuous_sInf_rng.2 fun t ht => ht.2.1 x
  have h2 : ∀ y : F, Continuous (fun x : E => x ⊗ₜ[ℂ] y) := fun y =>
    continuous_sInf_rng.2 fun t ht => ht.2.2 y
  -- hence sequentially continuous on `E × F` (`E` is an F-space) …
  have hseq : SeqContinuous (fun q : E × F => TensorProduct.mk ℂ E F q.1 q.2) :=
    SeparateContinuity.seqContinuous_of_separately_seqContinuous (𝕜 := ℂ) (TensorProduct.mk ℂ E F)
      (fun x => (h1 x).seqContinuous) (fun y => (h2 y).seqContinuous)
  -- … hence continuous, `E × F` being metrizable
  exact hseq.continuous
