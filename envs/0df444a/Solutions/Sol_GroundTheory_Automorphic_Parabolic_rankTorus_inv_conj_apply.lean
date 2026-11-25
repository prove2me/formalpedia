-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_inv_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:49.660712+00:00
-- url     : https://prove2.me/submissions/b85dc448-e7c8-433c-930b-5d397a35f770

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_uniformizer_ne_zero
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagGL_inv_conj_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (e : ℕ) (g : GL (Fin n) F) (i j : Fin n) :
    ((rankTorus F n β e)⁻¹ * g * rankTorus F n β e : GL (Fin n) F) i j =
      (GLnLocal.uniformizer F : F) ^ (((e * blockRank β i : ℕ) : ℤ) - ((e * blockRank β j : ℕ) : ℤ)) *
        g i j := by
  rw [rankTorus, torusPow, diagGL_inv_conj_apply]
  simp only [Units.val_zpow_eq_zpow_val, coe_uniformizerUnit, Units.val_inv_eq_inv_val]
  rw [zpow_sub₀ uniformizer_ne_zero, _root_.zpow_neg, _root_.zpow_neg, inv_inv]
  ring
end GroundTheory.Automorphic.Parabolic
