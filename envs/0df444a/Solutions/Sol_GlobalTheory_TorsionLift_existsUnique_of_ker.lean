-- Prove2me | solution 1 for GlobalTheory.TorsionLift.existsUnique_of_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:54.147119+00:00
-- url     : https://prove2.me/submissions/3c45c44f-f48b-40ac-8ff2-1675dd77345d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_GlobalTheory_laurentEval_single
import Theorems.Thm_GlobalTheory_torusCoord_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply
attribute [local simp] GlobalTheory.laurentEval_single
attribute [local simp] GlobalTheory.torusCoord_apply



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionLift
namespace GlobalTheory.TorsionLift
theorem _root_.solution {M M' : Type*} [CommGroup M] [CommGroup M'] (f : M →* M')
    (hf : Function.Surjective f) {N : ℕ} (hN : Function.Bijective fun z : f.ker => z ^ N)
    (y₀ : M') (hy₀ : y₀ ^ N = 1) : ∃! y, y ^ N = 1 ∧ f y = y₀ := by
  obtain ⟨y, hy⟩ := hf y₀
  have hker : y ^ N ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hy, hy₀]
  obtain ⟨z, hz⟩ := hN.2 ⟨y ^ N, hker⟩
  have hz' : (z : M) ^ N = y ^ N := congrArg Subtype.val hz
  have hfz : f z = 1 := (MonoidHom.mem_ker).1 z.2
  refine ⟨y * (z : M)⁻¹, ⟨?_, ?_⟩, ?_⟩
  · rw [mul_pow, inv_pow, hz', mul_inv_cancel]
  · rw [map_mul, map_inv, hy, hfz, inv_one, _root_.mul_one]
  · rintro w ⟨hw, hfw⟩
    have hmem : w * (y * (z : M)⁻¹)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_inv, hfw, hy, hfz, inv_one, _root_.mul_one,
        mul_inv_cancel]
    have h1 : (⟨_, hmem⟩ : f.ker) = 1 := by
      apply hN.1
      show (⟨_, hmem⟩ : f.ker) ^ N = 1 ^ N
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, one_pow, OneMemClass.coe_one]
      rw [mul_pow, inv_pow, hw, mul_pow, inv_pow, hz', mul_inv_cancel, inv_one, _root_.one_mul]
    exact mul_inv_eq_one.1 (congrArg Subtype.val h1)
end GlobalTheory.TorsionLift
