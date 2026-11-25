-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.ord_eq_zero_of_mem_unitsLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:58.610562+00:00
-- url     : https://prove2.me/submissions/34691396-9571-478c-87f8-6460f1eaa6b7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_mem_unitsLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.IdeleGroup
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} {n : ℕ}
    (h : finiteProj v x ∈ unitsLevel v n) : ord v x = 0 := by
  rw [ord, ← coe_finiteProj, (mem_unitsLevel.1 h).1, log_one, neg_zero]
end GroundTheory.Global.IdeleGroup
