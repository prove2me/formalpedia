-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.longestWeyl_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:31:06.762136+00:00
-- url     : https://prove2.me/submissions/88821ed1-3d46-4f70-8626-dff07442cd8b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.ContragredientTranspose.transposeHomeo_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open MeasureTheory Measure GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
namespace GroundTheory.Automorphic.ContragredientTranspose
theorem _root_.solution : (longestWeyl : GL (Fin n) F) * longestWeyl = 1 := by
  rw [longestWeyl, ← map_mul]
  have : (Fin.revPerm (n := n)) * Fin.revPerm = 1 := Equiv.ext fun i => by simp
  rw [this, map_one]
end GroundTheory.Automorphic.ContragredientTranspose
