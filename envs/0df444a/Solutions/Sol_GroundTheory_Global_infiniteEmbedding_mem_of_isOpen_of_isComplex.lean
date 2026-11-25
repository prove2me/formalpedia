-- Prove2me | solution 1 for GroundTheory.Global.infiniteEmbedding_mem_of_isOpen_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:03:03.897609+00:00
-- url     : https://prove2.me/submissions/c32aefda-354d-44bf-9beb-a9791da55613

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
import Theorems.Thm_GroundTheory_Global_Subgroup_mem_of_isOpen_complexUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_complexUnitsHom_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open IdeleGroup
namespace GroundTheory.Global
theorem _root_.solution (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsComplex)
    (a : (w.Completion)ˣ) : infiniteEmbedding w a ∈ H := by
  let Hc : Subgroup ℂˣ := (H.comap (infiniteEmbedding w)).comap (complexUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hc : Set ℂˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (complexUnitsHom hw).continuous
  have hmem := Subgroup.mem_of_isOpen_complexUnits Hc hopen
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw :
      w.Completion →+* ℂ).toMonoidHom a)
  rw [← complexUnitsHom_surjective hw a]
  exact hmem
end GroundTheory.Global
