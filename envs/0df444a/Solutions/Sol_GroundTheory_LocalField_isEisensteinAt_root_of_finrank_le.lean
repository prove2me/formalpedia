-- Prove2me | solution 1 for GroundTheory.LocalField.isEisensteinAt_root_of_finrank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:25:28.066615+00:00
-- url     : https://prove2.me/submissions/5644dbde-54dd-423d-81aa-bc13a5d10147

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Theorems.Thm_GroundTheory_LocalField_exists_addVal_eq_coe
import Theorems.Thm_GroundTheory_LocalField_natDegree_mul_addVal_eq_ramificationIndex
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_pos
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}
namespace GroundTheory.LocalField
theorem _root_.solution (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < f.natDegree) {α : 𝒪[L]} (hα : aeval α f = 0)
    (hdeg : Module.finrank K L ≤ f.natDegree) :
    ramificationIndex K L = f.natDegree ∧ Module.finrank K L = f.natDegree ∧ Irreducible α := by
  have key := natDegree_mul_addVal_eq_ramificationIndex hf hn hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [addVal_zero, ENat.mul_top (by exact_mod_cast hn.ne')] at key
    exact ENat.top_ne_natCast _ key
  obtain ⟨m, hm⟩ := exists_addVal_eq_coe hα0
  rw [hm] at key
  have key' : f.natDegree * m = ramificationIndex K L := by exact_mod_cast key
  have hef := ramificationIndex_mul_residueDegree K L
  have hf1 := residueDegree_pos K L
  have he := ramificationIndex_pos K L
  have hle : ramificationIndex K L ≤ Module.finrank K L := by
    rw [← hef]
    exact Nat.le_mul_of_pos_right _ hf1
  have hm1 : m = 1 := by
    rcases Nat.lt_or_ge m 1 with h | h
    · have : m = 0 := by omega
      rw [this, mul_zero] at key'
      omega
    · have : f.natDegree * m ≤ f.natDegree * 1 := by omega
      have := Nat.le_of_mul_le_mul_left this hn
      omega
  subst hm1
  rw [mul_one] at key'
  refine ⟨key'.symm, by omega, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible 𝒪[L]
  have : Associated ϖ α := by
    rw [← addVal_eq_iff_associated, addVal_uniformizer hϖ, hm, Nat.cast_one]
  exact this.irreducible hϖ
end GroundTheory.LocalField
