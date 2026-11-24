-- Prove2me | solution 1 for GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:09.224796+00:00
-- url     : https://prove2.me/submissions/2f3490d1-47f4-422d-b28a-65d6e1b779cc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEq
import Theorems.Thm_GlobalTheory_JR_CompanionCharpoly_companion_map
import Theorems.Thm_GlobalTheory_JR_CompanionCharpoly_coeff_universal

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
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  intro k _ r p i
  let f : MvPolynomial (Fin r) ℤ →+* k := MvPolynomial.eval₂Hom (Int.castRingHom k) p
  have hp : companion p = (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).map f := by
    rw [companion_map]
    congr 1
    funext j
    simp [f]
  rw [hp, Matrix.charpoly_map, Polynomial.coeff_map, coeff_universal]
  simp [f]
end GlobalTheory.JR.CompanionCharpoly
