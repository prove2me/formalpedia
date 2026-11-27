-- Prove2me | solution 1 for GlobalTheory.PrimeOrderScalar.sub_kill_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:39:14.894637+00:00
-- url     : https://prove2.me/submissions/41d62471-740e-4ed6-81d5-e2c6851829e7

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ActsBySameInteger
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Matrix
open GlobalTheory GlobalTheory.PrimeOrderScalar
open scoped TensorProduct
namespace GlobalTheory.PrimeOrderScalar
theorem _root_.solution {S M : Type} [CommRing S] [AddCommGroup M] [Module S M] (P P' X X' : S)
    (hP : ∀ m : M, P • m = 0) (m : M) : ((P + P') * X) • m = (X * P' + X' * P) • m := by
  simp only [add_mul, add_smul, mul_smul, hP, smul_zero, zero_add, add_zero]
  exact smul_comm _ _ _
end GlobalTheory.PrimeOrderScalar
