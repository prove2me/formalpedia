-- Prove2me | solution 1 for GlobalTheory.UniformSerre.comp_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:32.431851+00:00
-- url     : https://prove2.me/submissions/45018e8f-6fb9-45ac-b348-5a255f90e66c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
import Theorems.Thm_GlobalTheory_UniformSerre_coeff_comp
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
theorem _root_.solution (e : ℕ) (Q₁ Q₂ : MvPolynomial σ (reesAlgebra I)) :
    comp e (Q₁ - Q₂) = comp e Q₁ - comp e Q₂ := by
  ext m; rw [coeff_sub, coeff_comp, coeff_comp, coeff_comp, coeff_sub]
  exact Polynomial.coeff_sub _ _ _
end GlobalTheory.UniformSerre
