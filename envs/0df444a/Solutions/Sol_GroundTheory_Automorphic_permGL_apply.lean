-- Prove2me | solution 1 for GroundTheory.Automorphic.permGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:13.72612+00:00
-- url     : https://prove2.me/submissions/35ef1edc-275c-4c66-b394-4f2877267681

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (permGL k σ : Matrix (Fin n) (Fin n) k) i j = if i = σ j then 1 else 0 := by
  simp only [permGL, MonoidHom.coe_toHomUnits, permMatrixHom_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.inv_eq_iff_eq]
end GroundTheory.Automorphic
