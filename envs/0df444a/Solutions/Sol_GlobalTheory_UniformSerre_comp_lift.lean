-- Prove2me | solution 1 for GlobalTheory.UniformSerre.comp_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:03.465605+00:00
-- url     : https://prove2.me/submissions/ce8c70bf-7a1a-4a50-b00f-e9698b345471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
import Theorems.Thm_GlobalTheory_UniformSerre_coeff_comp
import Theorems.Thm_GlobalTheory_UniformSerre_coeff_lift
import Theorems.Thm_GlobalTheory_IsGradedMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformSerre
variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}
namespace GlobalTheory.UniformSerre
theorem _root_.solution (e e' : ℕ) (P : MvPolynomial σ R) (hP : ∀ m, coeff m P ∈ I ^ e) :
    comp e' (lift I e P) = if e' = e then P else 0 := by
  ext m
  rw [coeff_comp, coeff_lift]
  unfold liftFun; rw [dif_pos (hP m)]
  show (Polynomial.monomial e (coeff m P)).coeff e' = _
  rw [Polynomial.coeff_monomial]
  by_cases h : e' = e
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (Ne.symm h), if_neg h, coeff_zero]
end GlobalTheory.UniformSerre
