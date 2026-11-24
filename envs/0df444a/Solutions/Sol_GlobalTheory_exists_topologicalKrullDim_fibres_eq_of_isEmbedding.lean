-- Prove2me | solution 1 for GlobalTheory.exists_topologicalKrullDim_fibres_eq_of_isEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:39.791037+00:00
-- url     : https://prove2.me/submissions/b7ffd5ba-d86d-41b4-beb6-610022e8b129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
import Theorems.Thm_GlobalTheory_exists_affine_chart_trdeg_eq
import Theorems.Thm_GlobalTheory_topologicalKrullDim_preimage_genericPoint_eq
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology Limits
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
variable [IsDiscreteValuationRing O]
namespace GlobalTheory
theorem _root_.solution
    {S G : Type*} [TopologicalSpace S] [TopologicalSpace G]
    {i : S → Y} (hi : IsEmbedding i) (hr : Set.range i = f ⁻¹' {closedPoint O})
    {i' : G → Y} (hi' : IsEmbedding i')
    (hr' : Set.range i' = f ⁻¹' {genericPoint (Spec (.of O))}) :
    ∃ d : ℕ, topologicalKrullDim G = d ∧
      ∀ Z ∈ irreducibleComponents S, topologicalKrullDim Z = d := by
  obtain ⟨A, _, _, _, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq f (genericPoint Y)
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast O (A := A)
  rw [hA] at hd
  exact ⟨d, (topologicalKrullDim_eq_of_isEmbedding hi' hr').symm.trans
    (topologicalKrullDim_preimage_genericPoint_eq f hd),
    fun Z hZ ↦ topologicalKrullDim_eq_of_mem_irreducibleComponents_of_trdeg_eq f hi hr hZ hd⟩
end GlobalTheory
