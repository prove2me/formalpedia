-- Prove2me | solution 1 for GroundTheory.Global.range_algebraMap_sup_integralFiniteAdeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:37.789126+00:00
-- url     : https://prove2.me/submissions/6c8fb6cc-65d8-441f-aadc-3037e6a89878

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Theorems.Thm_GroundTheory_Global_exists_sub_mem_integralFiniteAdeles

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
theorem _root_.solution :
    (algebraMap K (FiniteAdeleRing R K)).range.toAddSubgroup ⊔
      (integralFiniteAdeles R K).toAddSubgroup = ⊤ := by
  refine eq_top_iff.mpr fun a _ => ?_
  obtain ⟨k, hk⟩ := exists_sub_mem_integralFiniteAdeles a
  have : a = algebraMap K (FiniteAdeleRing R K) k + (a - algebraMap K (FiniteAdeleRing R K) k) := by
    abel
  rw [this]
  exact AddSubgroup.add_mem_sup ⟨k, rfl⟩ hk
end GroundTheory.Global
