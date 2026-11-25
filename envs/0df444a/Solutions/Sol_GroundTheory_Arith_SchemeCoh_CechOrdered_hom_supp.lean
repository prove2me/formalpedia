-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.hom_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:32.465796+00:00
-- url     : https://prove2.me/submissions/b600b625-4266-4ee7-9770-c752fc0126b2

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_Supp_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_Supp_mapDomain

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
theorem _root_.solution : ∀ (q : ℕ) (i : Fin (q + 1) → ι), Supp (fun t => InRange i t) (hom q i)
  | 0, _ => Supp.zero
  | q + 1, i => by
    have hw : Supp (fun t => InRange i t)
        (Finsupp.single i 1 - proj (q + 1) i - lin (hom q) (bd q (Finsupp.single i 1))) := by
      refine ((Supp.single _ fun a => ⟨a, rfl⟩).sub
        ((proj_supp (q + 1) i).mono fun t ht => ht.2)).sub ?_
      rw [lin_bd_single_apply]
      exact Supp.sum _ _ fun a _ => ((solution q _).mono fun s hs => inRange_face a hs).smul _
    change Supp _ (Finsupp.mapDomain _ _)
    refine Supp.mapDomain _ hw fun t ht a => ?_
    cases a using Fin.cases with
    | zero => exact ⟨0, rfl⟩
    | succ a => simpa using ht a
end GroundTheory.Arith.SchemeCoh.CechOrdered
