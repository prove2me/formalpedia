-- Prove2me | solution 1 for GlobalTheory.NoetherInt.map_finSuccEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:25.959514+00:00
-- url     : https://prove2.me/submissions/98ddc4e0-e44a-4efb-96ef-2245b55e5085

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open MvPolynomial
variable {A : Type*} [CommRing A] {n : ℕ}
namespace GlobalTheory.NoetherInt
theorem _root_.solution {B : Type*} [CommRing B] (φ : A →+* B)
    (h : MvPolynomial (Fin (n + 1)) A) :
    Polynomial.map (MvPolynomial.map φ) (finSuccEquiv A n h) =
      finSuccEquiv B n (MvPolynomial.map φ h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.map_mul, hp]
    congr 1
    cases i using Fin.cases <;> simp [finSuccEquiv_X_zero, finSuccEquiv_X_succ]
end GlobalTheory.NoetherInt
