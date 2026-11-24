-- Prove2me | solution 1 for Neutral.B1.exists_isUniformiserAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:46:07.061337+00:00
-- url     : https://prove2.me/submissions/8b6a9484-3376-420a-8191-d23908b5a8e2

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
open Neutral Neutral.B1
variable (K : Type*) [Field K] [NumberField K]
namespace Neutral.B1
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    ∃ π : (v.adicCompletion K)ˣ, IsUniformiserAt K v (π : v.adicCompletion K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ h0, ϖ.2, hϖ⟩
end Neutral.B1
