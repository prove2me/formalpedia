-- Prove2me | solution 1 for GroundTheory.ProfCoh.valuation_smulPlace_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:29:46.109514+00:00
-- url     : https://prove2.me/submissions/d5f87ee1-0a94-48b7-81d9-c801a6808be0

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ValuationTransport
import Theorems.Thm_GroundTheory_ProfCoh_valuation_smulPlace

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
variable {F M : Type*} [Field F] [Field M] [NumberField M] [Algebra F M]
namespace GroundTheory.ProfCoh
theorem _root_.solution (σ : Gal(M/F)) (w : HeightOneSpectrum (𝓞 M)) (x : M) :
    (smulPlace σ w).valuation M x = w.valuation M (σ⁻¹ x) := by
  rw [← valuation_smulPlace σ w (σ⁻¹ x)]
  congr 1
  exact (AlgEquiv.apply_symm_apply σ x).symm
end GroundTheory.ProfCoh
