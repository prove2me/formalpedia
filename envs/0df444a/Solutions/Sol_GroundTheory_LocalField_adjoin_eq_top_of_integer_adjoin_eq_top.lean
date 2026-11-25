-- Prove2me | solution 1 for GroundTheory.LocalField.adjoin_eq_top_of_integer_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:52.079073+00:00
-- url     : https://prove2.me/submissions/66f0d7f8-a529-4bb7-9788-55a89c313b05

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_Different
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_isLocalization_integer
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤) :
    Algebra.adjoin K {algebraMap 𝒪[L] L x} = ⊤ := by
  have hle : ∀ z : 𝒪[L], (z : L) ∈ Algebra.adjoin K {algebraMap 𝒪[L] L x} := by
    intro z
    have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := by rw [hx]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.mp hy]
      exact Algebra.subset_adjoin rfl
    | algebraMap r =>
      rw [coe_algebraMap_integer]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz =>
      rw [Subring.coe_add]
      exact add_mem hy hz
    | mul y z _ _ hy hz =>
      rw [Subring.coe_mul]
      exact mul_mem hy hz
  have := isLocalization_integer K L
  rw [eq_top_iff]
  intro y _
  obtain ⟨⟨z, s⟩, hzs⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid 𝒪[L]
    (nonZeroDivisors 𝒪[K])) y
  obtain ⟨c, hc, hcs⟩ := s.2
  have hc0 : (c : K) ≠ 0 := by
    have : c ≠ 0 := nonZeroDivisors.ne_zero hc
    exact_mod_cast this
  have hy : y = (c : K)⁻¹ • (z : L) := by
    have h2 : ((s : 𝒪[L]) : L) = algebraMap K L c := by
      rw [← hcs]
      rfl
    simp only at hzs
    rw [Algebra.smul_def, map_inv₀, ← h2, eq_inv_mul_iff_mul_eq₀]
    · rw [mul_comm]; exact hzs
    · rw [h2]; exact (_root_.map_ne_zero _).mpr hc0
  rw [hy]
  exact Subalgebra.smul_mem _ (hle z) _
end GroundTheory.LocalField
