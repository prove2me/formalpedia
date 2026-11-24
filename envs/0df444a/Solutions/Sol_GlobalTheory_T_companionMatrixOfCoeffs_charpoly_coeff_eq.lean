-- Prove2me | solution 1 for GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:26.044523+00:00
-- url     : https://prove2.me/submissions/05dcc4b9-b42e-42dd-83e6-e852289f8678

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
import Theorems.Thm_GlobalTheory_JR_CompanionCharpoly_charpoly_companion_coeff_ring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  first | exact @GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | exact GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | (intros; apply GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring <;> assumption)
end _root_.GlobalTheory.T
