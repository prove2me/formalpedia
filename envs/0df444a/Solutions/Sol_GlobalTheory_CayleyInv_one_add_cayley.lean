-- Prove2me | solution 1 for GlobalTheory.CayleyInv.one_add_cayley
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:20.200289+00:00
-- url     : https://prove2.me/submissions/4c0ce7dc-c1e4-4b9d-baf7-4968909d8c37

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
    1 + (1 - g) * (1 + g)⁻¹ = (2 : R) • (1 + g)⁻¹ := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) + (1 - g) = (2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [two_smul]; abel
  calc 1 + (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := (Matrix.add_mul _ _ _).symm
    _ = (2 : R) • (1 + g)⁻¹ := by rw [h2, Matrix.smul_mul, Matrix.one_mul]
end GlobalTheory.CayleyInv
