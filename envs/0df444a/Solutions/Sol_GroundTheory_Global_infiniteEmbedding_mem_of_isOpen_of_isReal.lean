-- Prove2me | solution 1 for GroundTheory.Global.infiniteEmbedding_mem_of_isOpen_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:19:22.602502+00:00
-- url     : https://prove2.me/submissions/1c18b4f7-7380-46d0-9450-c870fc9f7d34

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
import Theorems.Thm_GroundTheory_Global_Subgroup_mem_of_isOpen_of_pos
import Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_realUnitsHom_surjective


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
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsReal)
    {a : (w.Completion)ˣ}
    (ha : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion)) :
    infiniteEmbedding w a ∈ H := by
  let Hr : Subgroup ℝˣ := (H.comap (infiniteEmbedding w)).comap (realUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hr : Set ℝˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (realUnitsHom hw).continuous
  let r : ℝˣ := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).toMonoidHom a
  have hr : 0 < (r : ℝ) := by
    change 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (a : w.Completion)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ha
  have hmem : r ∈ Hr := Subgroup.mem_of_isOpen_of_pos Hr hopen hr
  rw [← realUnitsHom_surjective hw a]
  exact hmem
end GroundTheory.Global
