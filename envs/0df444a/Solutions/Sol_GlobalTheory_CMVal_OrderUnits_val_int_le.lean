-- Prove2me | solution 1 for GlobalTheory.CMVal.OrderUnits.val_int_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:52.48781+00:00
-- url     : https://prove2.me/submissions/bd90ddcc-cab1-4127-9d51-ec82d8904cb9

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.OrderUnits
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (b : 𝓞 E) (hb : b ∈ P.asIdeal ^ n) :
    Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (P.intValuation_le_pow_iff_mem b n).2 hb
end GlobalTheory.CMVal.OrderUnits
