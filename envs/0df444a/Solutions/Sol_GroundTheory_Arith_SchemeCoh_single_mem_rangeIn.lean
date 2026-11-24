-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.single_mem_rangeIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:25.576133+00:00
-- url     : https://prove2.me/submissions/694886df-15d5-46c2-b0cc-ffa53e9ad2dc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (i : Fin (n + 1) → ι) (z : ℤ) :
    Finsupp.single i z ∈ Finsupp.supported ℤ ℤ (rangeIn (Set.range i)) :=
  Finsupp.single_mem_supported ℤ z (mem_rangeIn.2 subset_rfl)
end GroundTheory.Arith.SchemeCoh
