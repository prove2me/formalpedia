-- Prove2me | solution 1 for GroundTheory.Global.HeckeCharacter.idealCharacter_primeIdealUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:48:11.017927+00:00
-- url     : https://prove2.me/submissions/f445380e-673c-494d-8cc6-51acf917e3b9

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_idealCharacter_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.HeckeCharacter
open IdeleGroup
variable (χ : HeckeCharacter K)
namespace GroundTheory.Global.HeckeCharacter
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ χ.conductor) {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ)) :
    χ.idealCharacter ⟨primeIdealUnit v, primeIdealUnit_mem_idealsPrimeTo hv⟩ =
      χ.localComponent v π :=
  χ.idealCharacter_apply (finiteEmbedding_mem_primeToLevel hv π) _
    (toFractionalIdeal_finiteEmbedding_of_uniformizer hπ)
end GroundTheory.Global.HeckeCharacter
