-- Prove2me | solution 1 for GlobalTheory.TorsionZero.exists_homogenisation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:31.851518+00:00
-- url     : https://prove2.me/submissions/0e781aff-33e2-4a4e-a818-33982cd18ab2

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_NonemptyGradedAlgebraSubGrading

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
theorem _root_.solution (F : MvPolynomial σ K) (i : σ) :
    ∃ (n : ℕ) (G : MvPolynomial σ K), G.IsHomogeneous n ∧
      ∀ (S : Type) [CommRing S] [Algebra K S] (a : σ → S), a i = 1 → aeval a G = aeval a F := by
  refine ⟨F.totalDegree, ∑ n ∈ Finset.range (F.totalDegree + 1),
    homogeneousComponent n F * X i ^ (F.totalDegree - n), ?_, fun S _ _ a ha => ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun n hn => ?_
    have hn' := Finset.mem_range.mp hn
    have h1 := (homogeneousComponent_isHomogeneous n F).mul
      ((isHomogeneous_X K i).pow (F.totalDegree - n))
    have h2 : n + 1 * (F.totalDegree - n) = F.totalDegree := by omega
    rwa [h2] at h1
  · conv_rhs => rw [← sum_homogeneousComponent F]
    simp [map_sum, ha]
end GlobalTheory.TorsionZero
