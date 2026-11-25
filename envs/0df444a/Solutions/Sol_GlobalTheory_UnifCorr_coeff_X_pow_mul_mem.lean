-- Prove2me | solution 1 for GlobalTheory.UnifCorr.coeff_X_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:19:54.060371+00:00
-- url     : https://prove2.me/submissions/b179858a-a439-475a-857d-09625ae7f2bb

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
theorem _root_.solution (I : Ideal R) (i : σ) (k : ℕ) (G : MvPolynomial σ R)
    (h : ∀ m, coeff m G ∈ I) : ∀ m, coeff m ((X i : MvPolynomial σ R) ^ k * G) ∈ I := by
  intro m
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs
  · exact I.mul_mem_left _ (h _)
  · exact I.zero_mem
end GlobalTheory.UnifCorr
