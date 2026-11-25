-- Prove2me | solution 1 for GroundTheory.Global.ringOfIntegersToInteger_mem_maximalIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:59.271299+00:00
-- url     : https://prove2.me/submissions/fdb53c3f-f306-4dd3-a3cd-c803bb4c4149

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Inertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
open scoped WithZero Pointwise
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
namespace GroundTheory.Global
theorem _root_.solution (r : 𝓞 F) :
    ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] ↔ r ∈ u.asIdeal := by
  rw [← ker_toResidueInteger u, RingHom.mem_ker, toResidueInteger, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem]
end GroundTheory.Global
