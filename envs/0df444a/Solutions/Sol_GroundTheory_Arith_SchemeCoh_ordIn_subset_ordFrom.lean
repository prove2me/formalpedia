-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ordIn_subset_ordFrom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:49.945548+00:00
-- url     : https://prove2.me/submissions/1787f155-a7c1-47bd-aee2-b4dab5c3a78a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordFrom
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_le

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
theorem _root_.solution {n m : ℕ} (i : Fin (m + 1) → ι) :
    ordIn (n := n) (Set.range i) ⊆ ordFrom (minIdx i) := fun j hjr => by
  obtain ⟨hj, hr⟩ := mem_ordIn.1 hjr
  refine mem_ordFrom.2 ⟨hj, ?_⟩
  obtain ⟨a, ha⟩ := hr ⟨0, rfl⟩
  rw [← ha]
  exact minIdx_le i a
end GroundTheory.Arith.SchemeCoh
