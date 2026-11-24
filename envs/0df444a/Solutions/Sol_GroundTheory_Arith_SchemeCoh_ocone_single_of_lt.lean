-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ocone_single_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:51.419214+00:00
-- url     : https://prove2.me/submissions/58188e86-0085-4065-9ffc-5de16a19209a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains

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
theorem _root_.solution {n : ℕ} {s : ι} {i : Fin (n + 1) → ι} (h : s < i 0) (z : ℤ) :
    ocone s (Finsupp.single i z) = Finsupp.single (Fin.cons s i : Fin (n + 2) → ι) z := by
  rw [ocone, Finsupp.liftAddHom_apply_single, if_pos h]
  rfl
end GroundTheory.Arith.SchemeCoh
