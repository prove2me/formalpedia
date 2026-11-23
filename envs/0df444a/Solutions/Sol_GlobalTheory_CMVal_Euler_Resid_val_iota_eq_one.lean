-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.Resid.val_iota_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:01.895883+00:00
-- url     : https://prove2.me/submissions/cd340a14-b19c-40ee-b964-87953f0069b0

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_ReciprocityTheory_Automorphisms_PlaceA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitRepresentativesSplitPrime
import Theorems.Thm_GlobalTheory_CMVal_Euler_Resid_val_iota_lt_iff
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_one


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
theorem _root_.solution {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) {a : OF E}
    (ha : a ∉ q.asIdeal) : Valued.v (iota a P) = 1 :=
  le_antisymm (val_iota_le_one P a) (not_lt.1 fun h' => ha ((val_iota_lt_iff h a).1 h'))
end GlobalTheory.CMVal.Euler.Resid
