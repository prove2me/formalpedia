-- Prove2me | solution 1 for GlobalTheory.LatticeMinuscule.exists_mul_unit_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:49.406802+00:00
-- url     : https://prove2.me/submissions/1ea77760-9a27-4c7e-b310-fffd9a5b5a68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors
import Theorems.Thm_GlobalTheory_LatticeMinuscule_map_mulVec_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LatticeMinuscule
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
namespace GlobalTheory.LatticeMinuscule
theorem _root_.solution (C : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin n) (Fin n) R)
    (hP : IsUnit P.det) (y : Fin n → K) :
    (∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i))) ↔
      ∃ z : Fin n → R,
        y = (C * P.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i)) := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨P⁻¹.mulVec z, ?_⟩
    rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  · rintro ⟨z, rfl⟩
    exact ⟨P.mulVec z, by rw [← Matrix.mulVec_mulVec, map_mulVec_algebraMap]⟩
end GlobalTheory.LatticeMinuscule
