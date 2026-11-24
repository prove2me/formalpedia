-- Prove2me | solution 1 for GlobalTheory.CayleyInv.map_mul_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:09:25.625+00:00
-- url     : https://prove2.me/submissions/8be30ec9-3882-4752-9495-b35a132c7a5f

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
theorem _root_.solution (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    M.map σ * (M⁻¹).map σ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one σ (map_zero σ) (map_one σ)]
end GlobalTheory.CayleyInv
