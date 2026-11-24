-- Prove2me | solution 1 for GlobalTheory.TorsionZero.aeval_eq_zero_iff_components
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:32:57.340472+00:00
-- url     : https://prove2.me/submissions/1033c552-aa32-44f7-9030-cc37f6b0ca86

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading
import Theorems.Thm_GlobalTheory_TorsionZero_aeval_mem_of_isHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TorsionZero
open MvPolynomial
variable {K σ : Type} [Field K]
namespace GlobalTheory.TorsionZero
theorem _root_.solution {R : Type} [CommRing R] [Algebra K R] (𝒜 : ℕ → Submodule K R)
    [GradedAlgebra 𝒜] {x : σ → R} (hx : ∀ j, x j ∈ 𝒜 1) (G : MvPolynomial σ K) :
    aeval x G = 0 ↔ ∀ n, aeval x (homogeneousComponent n G) = 0 := by
  have hm : ∀ n, aeval x (homogeneousComponent n G) ∈ 𝒜 n := fun n => by
    simpa using aeval_mem_of_isHomogeneous 𝒜 hx (homogeneousComponent_isHomogeneous n G)
  constructor
  · intro h n
    by_cases hn : n ∈ Finset.range (G.totalDegree + 1)
    · rw [← sum_homogeneousComponent G, map_sum] at h
      have h2 := congrArg (GradedRing.proj 𝒜 n) h
      rw [map_sum, map_zero, Finset.sum_eq_single n] at h2
      · rwa [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hm n)] at h2
      · intro b _ hb
        rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hm b) hb]
      · exact fun h' => absurd hn h'
    · rw [homogeneousComponent_eq_zero _ _ (by simpa using hn), map_zero]
  · intro h
    rw [← sum_homogeneousComponent G, map_sum]
    exact Finset.sum_eq_zero fun n _ => h n
end GlobalTheory.TorsionZero
