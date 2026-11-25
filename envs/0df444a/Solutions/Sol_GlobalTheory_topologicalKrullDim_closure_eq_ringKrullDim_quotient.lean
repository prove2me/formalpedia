-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_closure_eq_ringKrullDim_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:10.833236+00:00
-- url     : https://prove2.me/submissions/28ff1562-2df1-4b34-96c9-b9e7694baddc

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Theorems.Thm_GlobalTheory_exists_affine_chart_over
import Theorems.Thm_GlobalTheory_topologicalKrullDim_range_inter_closure_eq
import Theorems.Thm_GlobalTheory_ringKrullDim_localizationAway_eq
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
import Theorems.Thm_GlobalTheory_topologicalKrullDim_le_of_forall_exists_isOpen


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
theorem _root_.solution {K : Type u} [Field K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p] {B : Type u} [CommRing B]
    (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B) :
    topologicalKrullDim (closure {j q} : Set Y) = ringKrullDim (B ⧸ q.asIdeal) := by
  rw [← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y, hy, hj'⟩ := exists_affine_chart_over p z.1
  have : Algebra.FiniteType K C := RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap K C))).mp (hj' ▸ inferInstance)
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y, hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y, hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show q' ∈ j' ⁻¹' Set.range j from ⟨q, hq'.symm⟩)
    (j.isOpenEmbedding.isOpen_range.preimage j'.continuous)
  have := q'.isPrime
  have hg' : Ideal.Quotient.mk q'.asIdeal g ≠ 0 := fun h ↦ hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [← ringKrullDim_localizationAway_eq K hg', ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have he := (j'.isOpenEmbedding.isEmbedding.comp
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk q'.asIdeal)
      Ideal.Quotient.mk_surjective).isEmbedding).comp
    (PrimeSpectrum.localization_comap_isEmbedding
      (Localization.Away (Ideal.Quotient.mk q'.asIdeal g))
      (Submonoid.powers (Ideal.Quotient.mk q'.asIdeal g)))
  refine (he.isInducing.codRestrict (s := Set.range j ∩ closure {j q})
    fun t ↦ ⟨hsub ?_, ?_⟩).topologicalKrullDim_le
  · intro h
    exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h
      (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk q'.asIdeal g)))
  · rw [← specializes_iff_mem_closure, ← hq']
    refine ((PrimeSpectrum.le_iff_specializes _ _).mp fun a ha ↦ ?_).map j'.continuous
    change algebraMap _ _ (Ideal.Quotient.mk q'.asIdeal a) ∈ t.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
    exact zero_mem _
end GlobalTheory
