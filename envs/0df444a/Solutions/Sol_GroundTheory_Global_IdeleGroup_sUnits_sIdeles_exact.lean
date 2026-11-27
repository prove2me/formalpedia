-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.sUnits_sIdeles_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:27.524921+00:00
-- url     : https://prove2.me/submissions/21bb0904-eaac-43be-ad61-50b1f2b1b41c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Theorems.Thm_GroundTheory_Global_IdeleGroup_sUnitsToSIdeles_injective

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S : Set (HeightOneSpectrum (𝓞 K)))
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (h : (diagonal K).range ⊔ sIdeles S = ⊤) :
    Function.Injective (sUnitsToSIdeles S) ∧
      (sUnitsToSIdeles S).range = (sIdelesToIdeleClassGroup S).ker ∧
      Function.Surjective (sIdelesToIdeleClassGroup S) :=
  ⟨sUnitsToSIdeles_injective S, range_sUnitsToSIdeles S,
    (sIdelesToIdeleClassGroup_surjective_iff S).2 h⟩
end GroundTheory.Global.IdeleGroup
