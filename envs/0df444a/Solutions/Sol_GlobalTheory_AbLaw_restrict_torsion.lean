-- Prove2me | solution 1 for GlobalTheory.AbLaw.restrict_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:25:35.710841+00:00
-- url     : https://prove2.me/submissions/71d3d65d-8508-4e90-8746-4bcdd4c3b42b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
import Theorems.Thm_GlobalTheory_AbLaw_secOn_basicOpen_localization
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {Y : Scheme.{0}} (M : LB Y)
variable {M}
namespace GlobalTheory.AbLaw
theorem _root_.solution (hM : M.IsLB) {V W W' : Y.Opens} (hW : IsAffineOpen W)
    (hW' : IsAffineOpen W') (h : W ≤ V) (e : W' ≤ W) (a : Γ(Y, V))
    (ha : W ⊓ Y.basicOpen a ≤ W') :
    (∀ y : SecOn M W, SecOn.restrict M e y = 0 → ∃ n : ℕ, rs Y h (a ^ n) • y = 0) ∧
      ∀ z : SecOn M W', ∃ (n : ℕ) (y : SecOn M W),
        SecOn.restrict M e y = rs Y (e.trans h) (a ^ n) • z := by
  have e₁ : W ⊓ Y.basicOpen a = Y.basicOpen (rs Y h a) := (Y.basicOpen_res a (homOfLE h).op).symm
  have e₂ : W ⊓ Y.basicOpen a = Y.basicOpen (rs Y (e.trans h) a) :=
    (le_antisymm (le_inf ha inf_le_right) (inf_le_inf_right _ e)).trans
      (Y.basicOpen_res a (homOfLE (e.trans h)).op).symm
  obtain ⟨k₁, c₁⟩ := secOn_basicOpen_localization Y M W _ _ inf_le_left hM hW.isCompact
    hW.isQuasiSeparated e₁
  obtain ⟨k₂, -⟩ := secOn_basicOpen_localization Y M W' _ _ ha hM hW'.isCompact
    hW'.isQuasiSeparated e₂
  refine ⟨fun y hy => ?_, fun z => ?_⟩
  · simp only [map_pow]
    refine k₁ y ?_
    rw [← SecOn.restrict_restrict e ha, hy, map_zero]
  · obtain ⟨n, x, hx⟩ := c₁ (SecOn.restrict M ha z)
    obtain ⟨m, hm⟩ := k₂ (SecOn.restrict M e x - rs Y (e.trans h) a ^ n • z) (by
      rw [map_sub, SecOn.restrict_restrict, hx, map_smulₛₗ, map_pow, rs_rs, rs_rs, sub_self])
    refine ⟨m + n, rs Y h a ^ m • x, ?_⟩
    rw [smul_sub, sub_eq_zero] at hm
    rw [map_smulₛₗ, map_pow, rs_rs, hm, map_pow, pow_add, mul_smul]
end GlobalTheory.AbLaw
