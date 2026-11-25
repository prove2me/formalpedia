-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.boundary_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:46.376298+00:00
-- url     : https://prove2.me/submissions/d7ae5c44-3736-4215-afb7-cd331c6a7c91

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_cone_add_cone_bd
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_rho_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_bd_rho
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_hmt_zero

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
    bd (n + 1) (hmt (n + 1) i) + lin (hmt n) (bd n (Finsupp.single i 1)) =
      Finsupp.single i 1 - rho (n + 1) i
  | n, i => by
    set y := Finsupp.single i 1 - rho (n + 1) i - lin (hmt n) (bd n (Finsupp.single i 1))
      with hydef
    have hby : bd n y = 0 := by
      rw [hydef, map_sub, map_sub, bd_rho]
      cases n with
      | zero => rw [lin_hmt_zero, lin_rho_zero, map_zero, sub_self, sub_zero]
      | succ n =>
        have ih := solution n
        have hlin : ∀ c : Chain ι (n + 1), bd (n + 1) (lin (hmt (n + 1)) c) =
            c - lin (rho (n + 1)) c - lin (hmt n) (bd n c) := by
          intro c
          have : (bd (n + 1)).comp (lin (hmt (ι := ι) (n + 1))) =
              AddMonoidHom.id _ - lin (rho (ι := ι) (n + 1)) - (lin (hmt (ι := ι) n)).comp (bd n) := by
            refine Finsupp.addHom_ext fun j z => ?_
            simp only [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
              lin_single, map_zsmul]
            rw [← Finsupp.smul_single_one j z, map_zsmul, map_zsmul, ← smul_sub, ← smul_sub,
              ← ih j, add_sub_cancel_right]
          exact congrArg (fun L => L c) this
        rw [hlin, bd_bd, map_zero, sub_zero]
        abel
    have key := bd_cone_add_cone_bd n (i 0) y
    rw [hby, map_zero, add_zero] at key
    change bd (n + 1) (cone (i 0) y) + _ = _
    rw [key, hydef, sub_add_cancel]
end GroundTheory.Arith.SchemeCoh
