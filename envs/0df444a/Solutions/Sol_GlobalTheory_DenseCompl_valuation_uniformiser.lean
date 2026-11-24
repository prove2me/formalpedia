-- Prove2me | solution 1 for GlobalTheory.DenseCompl.valuation_uniformiser
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:10:55.778242+00:00
-- url     : https://prove2.me/submissions/e363a3cb-2690-4688-b7a3-38622d8358ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousOfValuationEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqZeroOfForallLeExp
import Theorems.Thm_GlobalTheory_DenseCompl_asIdeal_eq_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open WithZero
open GlobalTheory GlobalTheory.DenseCompl
variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq]
namespace GlobalTheory.DenseCompl
theorem _root_.solution {π : W} (hπ : Irreducible π) (v : HeightOneSpectrum W) :
    v.valuation Qq (algebraMap W Qq π) = exp (-1) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_singleton hπ.ne_zero (asIdeal_eq_span hπ v)
end GlobalTheory.DenseCompl
