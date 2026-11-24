-- Prove2me | solution 1 for GroundTheory.ProfCoh.valuation_eq_exp_neg_ordAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:48.251861+00:00
-- url     : https://prove2.me/submissions/4d074a16-6b6d-4fe0-9c90-6dc668b6b8b8

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs

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
variable {F : Type*} [Field F] [NumberField F]
namespace GroundTheory.ProfCoh
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    v.valuation F (x : F) = WithZero.exp (-ordAt v x) := by
  rw [ordAt, neg_neg, ← valuationOfNeZero_eq]
  rfl
end GroundTheory.ProfCoh
