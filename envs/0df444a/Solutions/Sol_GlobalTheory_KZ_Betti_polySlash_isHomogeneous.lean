-- Prove2me | solution 1 for GlobalTheory.KZ.Betti.polySlash_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:58:48.657967+00:00
-- url     : https://prove2.me/submissions/a29de272-3a43-4f9e-ae78-fe309f40a67f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti
variable {R : Type} [CommRing R]
namespace GlobalTheory.KZ.Betti
theorem _root_.solution (m : Matrix (Fin 2) (Fin 2) ℤ) {p : MvPolynomial (Fin 2) R} {w : ℕ} (hp : p.IsHomogeneous w) :
    (slP m p).IsHomogeneous w := by
  have h1 := hp.aeval (fun i => (m i 0 : R) • MvPolynomial.X 0 + (m i 1 : R) • MvPolynomial.X 1)
    (n := 1) fun i => (MvPolynomial.homogeneousSubmodule (Fin 2) R 1).add_mem
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 0))
      ((MvPolynomial.homogeneousSubmodule (Fin 2) R 1).smul_mem _ (MvPolynomial.isHomogeneous_X R 1))
  rw [one_mul] at h1
  exact h1
end GlobalTheory.KZ.Betti
