-- Prove2me | solution 1 for GroundTheory.Global.Subgroup.mem_of_isOpen_complexUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:57:06.53644+00:00
-- url     : https://prove2.me/submissions/c59f17b0-d853-46bd-9ed0-b02881a0ac41

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup
import Theorems.Thm_GroundTheory_Global_Subgroup_subset_of_isPreconnected

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
namespace GroundTheory.Global
namespace Subgroup
theorem _root_.solution (H : Subgroup ℂˣ) (hH : IsOpen (H : Set ℂˣ)) (z : ℂˣ) :
    z ∈ H :=
  Subgroup.subset_of_isPreconnected H hH isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z)
end Subgroup
end GroundTheory.Global
