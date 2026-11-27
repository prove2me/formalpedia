-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.smul_eq_iff_localIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:36.261817+00:00
-- url     : https://prove2.me/submissions/69f4a436-1d00-4d42-9c7a-877f7d2b6f07

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
import Theorems.Thm_GroundTheory_Global_eq_of_localIdeal_eq
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
theorem _root_.solution (s : IdeleGroup K) (I J : 𝓘) :
    s • I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K), localIdeal (J : FractionalIdeal (𝓞 K)⁰ K) v =
      (localIdeal (I : FractionalIdeal (𝓞 K)⁰ K) v).map
        (LinearMap.mulLeft (v.adicCompletionIntegers K) ((s : 𝔸[K]).2 v)) := by
  constructor
  · rintro rfl v
    exact localIdeal_smul s I v
  · intro h
    refine Units.ext (eq_of_localIdeal_eq (Units.ne_zero _) (Units.ne_zero _) fun v ↦ ?_)
    rw [localIdeal_smul, h]
end GroundTheory.Global.IdeleGroup
