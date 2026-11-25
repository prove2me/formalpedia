-- Prove2me | solution 1 for GlobalTheory.UnifCorr.mem_of_coeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:27:04.421487+00:00
-- url     : https://prove2.me/submissions/1719115d-c57d-485b-8e46-ef713aca8877

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSectionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousCorrectionNextLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UnifCorr
variable {R : Type} [CommRing R] {σ : Type}
namespace GlobalTheory.UnifCorr
theorem _root_.solution (I : Ideal R) (K : Ideal (MvPolynomial σ R))
    (hC : ∀ a ∈ I, C a ∈ K) (G : MvPolynomial σ R) (h : ∀ m, coeff m G ∈ I) : G ∈ K := by
  rw [G.as_sum]
  refine K.sum_mem fun v _ => ?_
  rw [← mul_one (coeff v G), ← C_mul_monomial]
  exact K.mul_mem_right _ (hC _ (h v))
end GlobalTheory.UnifCorr
