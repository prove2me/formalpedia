-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:20.375039+00:00
-- url     : https://prove2.me/submissions/85a4a2fc-920e-4cd7-8b86-75437637fd30

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_aug_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_single_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordFrom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_strictMono_of_fin_one
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_ocone_add_ocone_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_ocone_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ordIn_subset_ordFrom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_rho_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_rho_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution : ∀ (n : ℕ) (i : Fin (n + 2) → ι),
    bd n (rho (n + 1) i) = lin (rho n) (bd n (Finsupp.single i 1))
  | 0, i => by
    have hx : lin (rho (ι := ι) 0) (bd 0 (Finsupp.single i 1)) ∈
        Finsupp.supported ℤ ℤ (ordFrom (minIdx i)) := by
      rw [lin_rho_zero]
      refine map_mem_supported _ (fun j hj z => ?_) (single_mem_rangeIn i 1)
      rw [bd_single]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
        (Finsupp.single_mem_supported ℤ z (mem_ordFrom.2 ⟨strictMono_of_fin_one _, ?_⟩))
      have hmem : (j ∘ k.succAbove) 0 ∈ Set.range i := (mem_rangeIn.1 hj) ⟨k.succAbove 0, rfl⟩
      obtain ⟨a, ha⟩ := hmem
      rw [← ha]
      exact minIdx_le i a
    rw [rho, bd_ocone_zero _ hx, lin_rho_zero, aug_bd, zero_smul, sub_zero]
  | n + 1, i => by
    have ih := solution n
    have hlin : ∀ c : Chain ι (n + 1), bd n (lin (rho (n + 1)) c) = lin (rho n) (bd n c) := by
      intro c
      have : (bd n).comp (lin (rho (ι := ι) (n + 1))) = (lin (rho (ι := ι) n)).comp (bd n) := by
        refine Finsupp.addHom_ext fun j z => ?_
        simp only [AddMonoidHom.comp_apply, lin_single, map_zsmul, ih]
        rw [← Finsupp.smul_single_one j z, map_zsmul, map_zsmul]
      exact congrArg (fun L => L c) this
    set x := lin (rho (n + 1)) (bd (n + 1) (Finsupp.single i 1)) with hxdef
    have hx : x ∈ Finsupp.supported ℤ ℤ (ordFrom (minIdx i)) := by
      refine Finsupp.supported_mono (ordIn_subset_ordFrom i) ?_
      refine map_mem_supported _ (fun j hj z => ?_) (bd_mem_rangeIn (single_mem_rangeIn i 1))
      rw [lin_single]
      exact Submodule.smul_mem _ z (Finsupp.supported_mono
        (fun k hk => mem_ordIn.2 ⟨(mem_ordIn.1 hk).1, (mem_ordIn.1 hk).2.trans (mem_rangeIn.1 hj)⟩)
        (rho_mem (n + 1) j))
    have hbx : bd n x = 0 := by rw [hxdef, hlin, bd_bd, map_zero]
    have key := bd_ocone_add_ocone_bd n (minIdx i) hx
    rw [hbx, map_zero, add_zero] at key
    change bd (n + 1) (ocone (minIdx i) x) = x
    exact key
end GroundTheory.Arith.SchemeCoh
