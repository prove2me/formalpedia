-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:26.03123+00:00
-- url     : https://prove2.me/submissions/8513bf1e-aeb9-4632-b75e-a473d642fbc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution : ¬ ((43 : ℕ) : ℤ) ∣ discr K := fun h => by
  have h0 : (discr K).natAbs ∣ 21 ^ Nat.totient 21 :=
    IsCyclotomicExtension.Rat.natAbs_discr 21 K ▸
      Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (by norm_num))
  have h₂ := (by norm_num : Nat.Prime 43).dvd_of_dvd_pow ((Int.natCast_dvd.1 h).trans h0)
  omega
end GlobalTheory.CMVal.InhabK
