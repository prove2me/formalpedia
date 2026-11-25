-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_ocone_add_ocone_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:37.661523+00:00
-- url     : https://prove2.me/submissions/591a4786-8d48-425b-bad0-25c38a01501f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_eq_of_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cone_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_cone_add_cone_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordFrom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_lt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_not_lt

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
theorem _root_.solution (n : ℕ) (s : ι) {c : Chain ι (n + 1)}
    (hc : c ∈ Finsupp.supported ℤ ℤ (ordFrom s)) :
    bd (n + 1) (ocone s c) + ocone s (bd n c) = c := by
  refine eq_of_supported (((bd (n + 1)).comp (ocone s)) + (ocone s).comp (bd n))
    (AddMonoidHom.id _) (fun j hj z => ?_) hc
  obtain ⟨hmono, hsj⟩ := mem_ordFrom.1 hj
  simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, AddMonoidHom.id_apply]
  have hface : ∀ k : Fin (n + 2), s ≤ (j ∘ k.succAbove) 0 := fun k =>
    hsj.trans (hmono.monotone (Fin.zero_le _))
  by_cases hlt : s < j 0
  · have h1 : ocone s (Finsupp.single j z) = cone s (Finsupp.single j z) := by
      rw [ocone_single_of_lt hlt, cone_single]
    have h2 : ocone s (bd n (Finsupp.single j z)) = cone s (bd n (Finsupp.single j z)) := by
      rw [bd_single, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, map_zsmul, ocone_single_of_lt (i := j ∘ k.succAbove)
        (show s < j (k.succAbove 0) from hlt.trans_le (hmono.monotone (Fin.zero_le _))),
        cone_single]
    rw [h1, h2]
    exact bd_cone_add_cone_bd n s _
  · have hs : s = j 0 := le_antisymm hsj (not_lt.1 hlt)
    rw [ocone_single_of_not_lt hlt, map_zero, zero_add, bd_single, map_sum, Fin.sum_univ_succ]
    have h0 : s < (j ∘ (0 : Fin (n + 2)).succAbove) 0 := by
      rw [hs]
      exact hmono (by simp)
    rw [map_zsmul, ocone_single_of_lt h0]
    have hrest : ∀ k : Fin (n + 1), ¬ s < (j ∘ k.succ.succAbove) 0 := fun k => by
      simp [Function.comp_apply, hs]
    simp only [map_zsmul, ocone_single_of_not_lt (hrest _), smul_zero, Finset.sum_const_zero,
      add_zero, Fin.val_zero, pow_zero, one_smul]
    congr 1
    rw [hs]
    exact Fin.cons_self_tail j
end GroundTheory.Arith.SchemeCoh
