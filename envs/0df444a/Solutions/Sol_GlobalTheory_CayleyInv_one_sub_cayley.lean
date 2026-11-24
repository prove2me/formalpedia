-- Prove2me | solution 1 for GlobalTheory.CayleyInv.one_sub_cayley
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:28.66211+00:00
-- url     : https://prove2.me/submissions/fa1b7a24-984e-41d8-ae2e-9534ce83e481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.CayleyInv
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 - (1 - g) * (1 + g)⁻¹ = (2 : R) • (g * (1 + g)⁻¹) := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) - (1 - g) = (2 : R) • g := by
    rw [two_smul]; abel
  calc 1 - (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := (Matrix.sub_mul _ _ _).symm
    _ = (2 : R) • (g * (1 + g)⁻¹) := by rw [h2, Matrix.smul_mul]
end GlobalTheory.CayleyInv
