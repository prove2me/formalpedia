-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_ocone_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:10.542795+00:00
-- url     : https://prove2.me/submissions/57d4ebc3-452e-43d2-bac1-4a50459adca2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_aug_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_of_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordFrom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_lt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_not_lt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cons_comp_succAbove_zero


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
theorem _root_.solution (s : ι) {c : Chain ι 0} (hc : c ∈ Finsupp.supported ℤ ℤ (ordFrom s)) :
    bd 0 (ocone s c) = c - aug c • Finsupp.single (fun _ => s) 1 := by
  refine eq_of_supported ((bd 0).comp (ocone s))
    (AddMonoidHom.id _ - (zmultiplesHom _ (Finsupp.single (fun _ => s) 1)).comp aug)
    (fun j hj z => ?_) hc
  obtain ⟨-, hsj⟩ := mem_ordFrom.1 hj
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
    zmultiplesHom_apply, aug_single, Finsupp.smul_single_one]
  have hconst : (fun _ : Fin 1 => s) = Fin.cons s j ∘ (1 : Fin 2).succAbove := by
    funext a
    rw [Fin.fin_one_eq_zero a]
    rfl
  by_cases hlt : s < j 0
  · rw [ocone_single_of_lt hlt, bd_single, Fin.sum_univ_two, cons_comp_succAbove_zero, ← hconst]
    simp [sub_eq_add_neg]
  · have hj : j = fun _ => s := by
      funext a
      rw [Fin.fin_one_eq_zero a]
      exact (le_antisymm hsj (not_lt.1 hlt)).symm
    rw [ocone_single_of_not_lt hlt, map_zero, hj, sub_self]
end GroundTheory.Arith.SchemeCoh
