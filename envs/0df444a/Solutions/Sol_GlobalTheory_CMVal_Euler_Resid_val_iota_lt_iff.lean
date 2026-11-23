-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.Resid.val_iota_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:15.862669+00:00
-- url     : https://prove2.me/submissions/39b24ac0-733f-456f-9e7a-101cb044e0a0

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitRepresentativesSplitPrime
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_le_exp_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.Resid
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.Resid
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) (a : OF E) :
    Valued.v (iota a P) < 1 ↔ a ∈ q.asIdeal := by
  rw [← le_exp_iff, val_iota_le_iff, pow_one, ← Ideal.mem_comap, h]
end GlobalTheory.CMVal.Euler.Resid
