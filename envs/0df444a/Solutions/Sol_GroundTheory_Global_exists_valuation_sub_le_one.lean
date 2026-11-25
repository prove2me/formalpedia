-- Prove2me | solution 1 for GroundTheory.Global.exists_valuation_sub_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:51.170923+00:00
-- url     : https://prove2.me/submissions/dc81cb9a-4aca-40e1-9f20-98277a8072e0

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0
import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GroundTheory.Global
theorem _root_.solution (S : Finset (HeightOneSpectrum R))
    (x : HeightOneSpectrum R → K) :
    ∃ k : K, (∀ v ∈ S, v.valuation K (k - x v) ≤ 1) ∧ (∀ v ∉ S, v.valuation K k ≤ 1) :=
  _root_.P2M_UpperTheory_Reformulated_B_ExistsValuationSubLeOne_exists_valuation_sub_le_one__2c694883c8a0 S x
end GroundTheory.Global
