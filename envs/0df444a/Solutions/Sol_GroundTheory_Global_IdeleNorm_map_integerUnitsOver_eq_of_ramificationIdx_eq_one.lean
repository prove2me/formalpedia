-- Prove2me | solution 1 for GroundTheory.Global.IdeleNorm.map_integerUnitsOver_eq_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:44:29.809842+00:00
-- url     : https://prove2.me/submissions/d4f02a67-a3d1-48cd-9a57-65d7bae7642f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormGroups
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalNormsEverywhere
import Theorems.Thm_GroundTheory_Global_IdeleNorm_exists_norm_eq_of_ramificationIdx_eq_one
import Theorems.Thm_GroundTheory_Global_IdeleNorm_finiteLocalNorm_mulSingle
import Theorems.Thm_GroundTheory_Global_IdeleNorm_map_integerUnitsOver_le


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
open IsDedekindDomain NumberField Filter
open AdeleBaseChange SemiLocal
noncomputable section
open GroundTheory.Global.IdeleNorm
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
namespace GroundTheory.Global.IdeleNorm
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K))
    (w : PlacesOver L v) (he : w.1.asIdeal.ramificationIdx (𝓞 K) = 1) :
    (integerUnitsOver L v).map (finiteLocalNorm L v) =
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by
  classical
  refine le_antisymm (map_integerUnitsOver_le v) fun u hu ↦ ?_
  obtain ⟨y, hy, hyu⟩ := exists_norm_eq_of_ramificationIdx_eq_one v w.1 he hu
  refine ⟨Pi.mulSingle w y, mem_integerUnitsOver.2 fun w' ↦ ?_, ?_⟩
  · by_cases h : w' = w
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact hy
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  · rw [finiteLocalNorm_mulSingle]
    exact Units.ext hyu
end GroundTheory.Global.IdeleNorm
