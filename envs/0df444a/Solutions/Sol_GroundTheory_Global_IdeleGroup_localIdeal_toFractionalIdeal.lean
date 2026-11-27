-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.localIdeal_toFractionalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:45:46.204682+00:00
-- url     : https://prove2.me/submissions/5f955325-7cf8-4c2f-b768-2a3ba34e28dd

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_IdeleGroup_smul_one_eq_toFractionalIdeal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_localIdeal_smul

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
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
local notation "𝓘" => (FractionalIdeal (𝓞 K)⁰ K)ˣ
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (s : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    localIdeal ((toFractionalIdeal s : 𝓘) : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  rw [← smul_one_eq_toFractionalIdeal, localIdeal_smul, Units.val_one]
end GroundTheory.Global.IdeleGroup
