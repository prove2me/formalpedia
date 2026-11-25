-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_range_inter_closure_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:45:30.743392+00:00
-- url     : https://prove2.me/submissions/80d15595-2814-41b1-baaa-9bccaa606c81

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding


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
open AlgebraicGeometry CategoryTheory Topology
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{u}} {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B) :
    topologicalKrullDim (Set.range j ∩ closure {j q} : Set Y) = ringKrullDim (B ⧸ q.asIdeal) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  refine topologicalKrullDim_eq_of_isEmbedding (j.isOpenEmbedding.isEmbedding.comp
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q.asIdeal)
      Ideal.Quotient.mk_surjective).isEmbedding) ?_
  refine (Set.range_comp _ _).trans
    (.trans (congrArg (Set.image j) ?_) Set.image_preimage_eq_range_inter)
  refine (range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).trans ?_
  rw [Ideal.mk_ker]
  exact (PrimeSpectrum.closure_singleton q).symm.trans
    ((j.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image _).trans
      (congrArg (fun s ↦ j ⁻¹' closure s) Set.image_singleton))
end GlobalTheory
