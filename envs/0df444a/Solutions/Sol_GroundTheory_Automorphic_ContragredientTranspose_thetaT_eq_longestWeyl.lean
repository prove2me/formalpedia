-- Prove2me | solution 1 for GroundTheory.Automorphic.ContragredientTranspose.thetaT_eq_longestWeyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:37:16.471035+00:00
-- url     : https://prove2.me/submissions/bb9b1cc8-5e09-44d1-bbe4-fd2d3d6603d7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_longestWeyl_mul_self
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_thetaT_apply
import Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_transposeHomeo_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaMat_eq
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
theorem _root_.solution (g : GL (Fin n) F) :
    thetaT g = longestWeyl * theta g * longestWeyl := by
  have hs : sigma g = longestWeyl * transposeGL g * longestWeyl :=
    Units.ext (by rw [coe_sigma, sigmaMat_eq, Units.val_mul, Units.val_mul, coe_transposeGL]; rfl)
  have hw : (longestWeyl : GL (Fin n) F)⁻¹ = longestWeyl :=
    inv_eq_of_mul_eq_one_right longestWeyl_mul_self
  rw [theta, hs, thetaT_apply]
  simp only [_root_.mul_inv_rev, hw, mul_assoc, longestWeyl_mul_self, mul_one]
  rw [← mul_assoc, longestWeyl_mul_self, one_mul]
end GroundTheory.Automorphic.ContragredientTranspose
