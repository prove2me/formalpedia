-- Prove2me | solution 1 for GroundTheory.Global.multiplicity_relDiscr_semiLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:27.546042+00:00
-- url     : https://prove2.me/submissions/acc35a22-e7c9-4356-8e83-490ec4e358b1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
import Theorems.Thm_GroundTheory_Global_multiplicity_differentIdeal_eq_differentExponent
import Theorems.Thm_GroundTheory_Global_multiplicity_relDiscr_eq_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open SemiLocal
namespace GroundTheory.Global
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : PlacesOver M v, w.1.asIdeal.inertiaDeg (𝓞 K) *
        differentExponent (v.adicCompletion K) (w.1.adicCompletion M) := by
  rw [multiplicity_relDiscr_eq_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [multiplicity_differentIdeal_eq_differentExponent v w.1]
end GroundTheory.Global
