-- Prove2me | solution 1 for GroundTheory.Global.Artin.extendByZero_conjFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:56:42.938415+00:00
-- url     : https://prove2.me/submissions/e9fa3710-8eca-47ca-ba86-d6b0eda9adb9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_of_mem
import Theorems.Thm_GroundTheory_Global_Artin_extendByZero_of_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
namespace GroundTheory.Global.Artin
theorem _root_.solution (H D : Subgroup G) (x : G) (f : H → ℂ) (y : D) :
    extendByZero _ (conjFun H D x f) y = extendByZero H f (x * y * x⁻¹) := by
  by_cases hy : y ∈ (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D
  · rw [extendByZero_of_mem _ _ hy, extendByZero_of_mem H f
      ((mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 hy))]
    rfl
  · have hy' : x * (y : G) * x⁻¹ ∉ H := fun h ↦
      hy (Subgroup.mem_subgroupOf.2 ((mem_conj_inv_smul_iff H x _).2 h))
    rw [extendByZero_of_notMem _ _ hy, extendByZero_of_notMem H f hy']
end GroundTheory.Global.Artin
