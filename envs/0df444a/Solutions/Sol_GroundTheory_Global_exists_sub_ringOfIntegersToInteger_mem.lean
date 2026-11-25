-- Prove2me | solution 1 for GroundTheory.Global.exists_sub_ringOfIntegersToInteger_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:31.852555+00:00
-- url     : https://prove2.me/submissions/1f80e526-cd4e-4dc2-b72f-11ea84172a61

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
theorem _root_.solution (x : 𝒪[u.adicCompletion F]) :
    ∃ r : 𝓞 F, x - ringOfIntegersToInteger u r ∈ 𝓂[u.adicCompletion F] := by
  obtain ⟨r, hr⟩ := toResidueInteger_surjective u (Ideal.Quotient.mk _ x)
  exact ⟨r, Ideal.Quotient.eq.1 hr.symm⟩
end GroundTheory.Global
