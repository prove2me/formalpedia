-- Prove2me | solution 1 for MasulloGRH.indTensor_isHLCS
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:09:34.641859+00:00
-- url     : https://prove2.me/submissions/387e00ae-5df7-4505-b420-97c38c2b29d7

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_epsTensor_isHLCS
import Theorems.Thm_MasulloGRH_indTensor_le_projTensor_le_epsTensor

open TensorProduct Topology Filter
set_option autoImplicit false
universe u v

open MasulloGRH

namespace Sol_MasulloGRH_indTensor_isHLCS

/-- The infimum of a set of locally convex topologies on a complex vector space is a locally
convex topology: it is defined by the family of all seminorms that are continuous for it. -/
theorem isLocallyConvexTopology_sInf {X : Type u} [AddCommGroup X] [Module ℂ X]
    (ts : Set (TopologicalSpace X)) (h : ∀ t ∈ ts, IsLocallyConvexTopology X t) :
    IsLocallyConvexTopology X (sInf ts) := by
  have hP : @PolynormableSpace ℂ X _ _ _ (sInf ts) := by
    refine PolynormableSpace.sInf ?_
    intro t ht
    obtain ⟨ι, _, p, hp⟩ := h t ht
    let _ : TopologicalSpace X := t
    exact hp.toPolynormableSpace
  let _ : TopologicalSpace X := sInf ts
  exact ⟨{p : Seminorm ℂ X // Continuous p}, ⟨⟨0, continuous_const⟩⟩, _,
    PolynormableSpace.withSeminorms ℂ X⟩

/-- A topology finer than a Hausdorff topology is Hausdorff. -/
theorem t2Space_of_le {X : Type u} {t₁ t₂ : TopologicalSpace X} (hle : t₁ ≤ t₂)
    (h₂ : @T2Space X t₂) : @T2Space X t₁ :=
  @T2Space.of_injective_continuous X X t₁ t₂ h₂ id Function.injective_id
    (continuous_id_iff_le.2 hle)

end Sol_MasulloGRH_indTensor_isHLCS

open Sol_MasulloGRH_indTensor_isHLCS

theorem solution (E F : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] (hE : IsHLCS E) (hF : IsHLCS F) :
    @IsHLCS (E ⊗[ℂ] F) _ _ (indTensorTopology E F) := by
  refine ⟨?_, ?_⟩
  · -- `ι` is the infimum of a set of locally convex topologies
    exact isLocallyConvexTopology_sInf _ (fun t ht => ht.1)
  · -- `ι` is finer than `ε`, which is Hausdorff
    have hle : indTensorTopology E F ≤ epsTensorTopology E F :=
      (indTensor_le_projTensor_le_epsTensor E F hE hF).1.trans
        (indTensor_le_projTensor_le_epsTensor E F hE hF).2
    exact t2Space_of_le hle (epsTensor_isHLCS E F hE hF).2
