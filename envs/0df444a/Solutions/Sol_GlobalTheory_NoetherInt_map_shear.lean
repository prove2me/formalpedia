-- Prove2me | solution 1 for GlobalTheory.NoetherInt.map_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:26.929791+00:00
-- url     : https://prove2.me/submissions/ff49e028-5395-4c1c-84cd-2b304f9a71f8

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
theorem _root_.solution {B : Type*} [CommRing B] (φ : A →+* B) (u : ℕ)
    (g : MvPolynomial (Fin (n + 1)) A) :
    MvPolynomial.map φ (shear A n u g) = shear B n u (MvPolynomial.map φ g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [shear, shearHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    cases i using Fin.cases <;> simp [shear, shearHom]
end GlobalTheory.NoetherInt
