-- Prove2me | solution 1 for Neutral.B1.valued_algebraMap_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:14.245225+00:00
-- url     : https://prove2.me/submissions/ed2b616d-6ccf-408d-af6d-1a9d02617507

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (y : 𝓞 K) (hy : y ∉ v.asIdeal) :
    Valued.v (algebraMap K (v.adicCompletion K) (y : K)) = 1 := by
  have e : algebraMap K (v.adicCompletion K) (y : K) =
      ((algebraMap (𝓞 K) K y : K) : v.adicCompletion K) := rfl
  rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact hy
end Neutral.B1
