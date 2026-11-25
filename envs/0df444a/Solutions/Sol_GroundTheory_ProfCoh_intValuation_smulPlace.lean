-- Prove2me | solution 1 for GroundTheory.ProfCoh.intValuation_smulPlace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:14.35925+00:00
-- url     : https://prove2.me/submissions/da2d0f08-a1bc-40bf-822c-8942c0762d80

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
import Theorems.Thm_GroundTheory_ProfCoh_eq_of_forall_le_exp_iff
import Theorems.Thm_GroundTheory_ProfCoh_smulPlace_asIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Pointwise
variable {B : Type*} [CommRing B] [IsDedekindDomain B] {G : Type*} [Group G]
  [MulSemiringAction G B]
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : G) (w : HeightOneSpectrum B) (r : B) :
    (smulPlace σ w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, map_zero, map_zero]
  have hσr : σ • r ≠ 0 := fun h => hr (by rw [← inv_smul_smul σ r, h, smul_zero])
  refine eq_of_forall_le_exp_iff (intValuation_ne_zero _ _ hσr) (intValuation_ne_zero _ _ hr)
    (intValuation_le_one _ _) (intValuation_le_one _ _) fun n => ?_
  rw [intValuation_le_pow_iff_mem, intValuation_le_pow_iff_mem, smulPlace_asIdeal, ← smul_pow']
  exact Ideal.smul_mem_pointwise_smul_iff
end GroundTheory.ProfCoh
