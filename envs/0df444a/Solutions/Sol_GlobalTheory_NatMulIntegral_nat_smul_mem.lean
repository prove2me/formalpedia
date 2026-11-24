-- Prove2me | solution 1 for GlobalTheory.NatMulIntegral.nat_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:02:55.257967+00:00
-- url     : https://prove2.me/submissions/dccc37dc-450a-43b9-b2aa-afda2439103a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNatSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulIntegral
open NumberField
namespace GlobalTheory.NatMulIntegral
theorem _root_.solution {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (d : ℕ) {x : Fin n → E} (hx : x ∈ L) :
    (d : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx d
end GlobalTheory.NatMulIntegral
