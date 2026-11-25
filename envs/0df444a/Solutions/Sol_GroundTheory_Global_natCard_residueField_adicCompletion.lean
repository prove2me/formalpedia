-- Prove2me | solution 1 for GroundTheory.Global.natCard_residueField_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:51.758596+00:00
-- url     : https://prove2.me/submissions/f33d3dd9-773b-47ce-ac38-6ad4feb3052e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Theorems.Thm_GroundTheory_Global_natCard_residueField_adicCompletionIntegers


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
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
  GroundTheory.LocalField
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution :
    Nat.card 𝓀[v.adicCompletion K] = Ideal.absNorm v.asIdeal := by
  rw [← natCard_residueField_adicCompletionIntegers v]
  exact Nat.card_congr
    (IsLocalRing.ResidueField.mapEquiv (integerEquivAdicCompletionIntegers v)).toEquiv
end GroundTheory.Global
