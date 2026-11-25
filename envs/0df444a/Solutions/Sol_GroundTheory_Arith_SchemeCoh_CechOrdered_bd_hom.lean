-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.bd_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:37.397316+00:00
-- url     : https://prove2.me/submissions/3223494a-d4d8-46de-a90d-11631789cc7f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_sub__d1eb2e601553
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_CechOrdered_lin_zero__464d3f8172ad

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
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution : ∀ (q : ℕ) (i : Fin (q + 2) → ι),
    bd (q + 1) (hom (q + 1) i) =
      Finsupp.single i 1 - proj (q + 1) i - lin (hom q) (bd q (Finsupp.single i 1))
  | 0, i => by
    change bd 1 (cone (i 0) _) = _
    rw [bd_cone]
    have : bd 0 (Finsupp.single i 1 - proj 1 i - lin (hom 0) (bd 0 (Finsupp.single i 1))) = 0 := by
      rw [map_sub, map_sub, bd_proj, show hom 0 = fun _ => 0 from rfl, lin_zero', map_zero]
      rw [show lin (proj 0) (bd 0 (Finsupp.single i 1)) = bd 0 (Finsupp.single i 1) from
        lin_single_id _]
      simp
    rw [this, map_zero, sub_zero]
  | q + 1, i => by
    change bd (q + 2) (cone (i 0) _) = _
    rw [bd_cone]
    have : bd (q + 1) (Finsupp.single i 1 - proj (q + 2) i -
        lin (hom (q + 1)) (bd (q + 1) (Finsupp.single i 1))) = 0 := by
      rw [map_sub, map_sub, bd_proj, ← lin_comp]
      simp only [solution q]
      rw [lin_sub', lin_sub', lin_single_id, lin_bd_single, bd_bd, map_zero]
      abel
    rw [this, map_zero, sub_zero]
end GroundTheory.Arith.SchemeCoh.CechOrdered
