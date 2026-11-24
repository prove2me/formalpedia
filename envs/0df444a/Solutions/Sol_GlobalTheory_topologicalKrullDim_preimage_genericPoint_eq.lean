-- Prove2me | solution 1 for GlobalTheory.topologicalKrullDim_preimage_genericPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:02.150603+00:00
-- url     : https://prove2.me/submissions/d0397a9c-e0b1-48b6-91b9-9678a1090f48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_isEmbedding
import Theorems.Thm_GlobalTheory_topologicalKrullDim_eq_of_forall_exists_isOpen
import Theorems.Thm_GlobalTheory_exists_affine_chart_trdeg_eq

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
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace GlobalTheory
theorem _root_.solution {d : ℕ}
    (hd : letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
      Algebra.trdeg O Y.functionField = d) :
    topologicalKrullDim (f ⁻¹' {genericPoint (Spec (.of O))} : Set Y) = d := by
  have hgen : genericPoint (Spec (.of O)) = (⟨⊥, inferInstance⟩ : PrimeSpectrum O) :=
    genericPoint_eq_bot_of_affine (.of O)
  refine topologicalKrullDim_eq_of_forall_exists_isOpen ?_ fun x _ ↦ ?_
  · obtain ⟨A, _, _, _, _, _, j, _, -, hj, -⟩ :=
      exists_affine_chart_trdeg_eq f (genericPoint Y)
    refine ⟨j (⟨⊥, inferInstance⟩ : PrimeSpectrum A), ?_⟩
    change (j ≫ f) _ = _
    rw [hj, hgen]
    exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective O A))
  · obtain ⟨A, _, _, _, _, _, j, _, hx, hj, hA⟩ := exists_affine_chart_trdeg_eq f x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
    have := IsLocalization.tensorRight (S := A) (FractionRing O) (nonZeroDivisors O)
    rw [← ringKrullDim_genericFibre_eq O (FractionRing O) (hA.trans hd),
      ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    refine topologicalKrullDim_eq_of_isEmbedding (j.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.localization_comap_isEmbedding (FractionRing O ⊗[O] A)
        (Algebra.algebraMapSubmonoid A (nonZeroDivisors O)))) ?_
    refine (Set.range_comp _ _).trans
      (.trans (congrArg (Set.image j) ?_) Set.image_preimage_eq_range_inter)
    refine (PrimeSpectrum.localization_comap_range _
      (Algebra.algebraMapSubmonoid A (nonZeroDivisors O))).trans ?_
    ext p
    change _ ↔ (j ≫ f) p = _
    rw [hj, hgen]
    change Disjoint _ _ ↔ PrimeSpectrum.comap (algebraMap O A) p = _
    rw [PrimeSpectrum.ext_iff, PrimeSpectrum.comap_asIdeal, eq_bot_iff, Set.disjoint_left]
    constructor
    · intro h a ha
      by_contra h0
      exact h ⟨a, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ ha
    · rintro h _ ⟨a, ha, rfl⟩ hp
      exact nonZeroDivisors.ne_zero ha (h hp)
end GlobalTheory
