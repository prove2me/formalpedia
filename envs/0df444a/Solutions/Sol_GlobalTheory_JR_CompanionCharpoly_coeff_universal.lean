-- Prove2me | solution 1 for GlobalTheory.JR.CompanionCharpoly.coeff_universal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:19:52.905698+00:00
-- url     : https://prove2.me/submissions/3efffb4e-5784-456f-ae02-4af51fc9e1f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEq
import Theorems.Thm_GlobalTheory_JR_CompanionCharpoly_companion_map
import Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_coeff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.CompanionCharpoly
namespace GlobalTheory.JR.CompanionCharpoly
theorem _root_.solution (r : ℕ) (i : Fin r) :
    (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).charpoly.coeff (i : ℕ) =
      MvPolynomial.X i := by
  set R := MvPolynomial (Fin r) ℤ
  set K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  apply hinj
  have h := GlobalTheory.JR.NormalFormL.charpoly_companion_coeff
    (fun j : Fin r => algebraMap R K (MvPolynomial.X j)) i
  rw [← companion_map, Matrix.charpoly_map, Polynomial.coeff_map] at h
  exact h
end GlobalTheory.JR.CompanionCharpoly
