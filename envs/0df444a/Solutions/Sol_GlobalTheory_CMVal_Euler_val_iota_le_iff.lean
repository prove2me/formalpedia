-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.val_iota_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:02.16695+00:00
-- url     : https://prove2.me/submissions/59f5212e-0383-432b-b7c3-e549915d2e9b

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (a : OF E) :
    Valued.v (iota a P) ≤ WithZero.exp (-(n : ℤ)) ↔ algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal ^ n := by
  have : iota a = algebraMap E (Af E) (algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)) := rfl
  rw [this, FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact P.intValuation_le_pow_iff_mem _ n
end GlobalTheory.CMVal.Euler
