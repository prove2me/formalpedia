-- Prove2me | solution 1 for GlobalTheory.LatticeMinuscule.map_mulVec_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:43:50.496516+00:00
-- url     : https://prove2.me/submissions/5eda57eb-cd37-4dd9-9484-01a2b5e5b911

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    (M.map (algebraMap R K)).mulVec (fun i => algebraMap R K (z i))
      = fun i => algebraMap R K (M.mulVec z i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl
end GlobalTheory.LatticeMinuscule
