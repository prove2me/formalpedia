-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cone_mem_rangeIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:08.024799+00:00
-- url     : https://prove2.me/submissions/ec6cba94-2e33-4834-9870-4164649116c7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_rangeIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cone_single

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
theorem _root_.solution {n : ℕ} {S : Set ι} {s : ι} (hs : s ∈ S) {c : Chain ι n}
    (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    cone s c ∈ Finsupp.supported ℤ ℤ (rangeIn S) :=
  map_mem_supported _ (fun j hj z => by
    rw [cone_single]
    refine Finsupp.single_mem_supported ℤ z (mem_rangeIn.2 ?_)
    rintro x ⟨a, rfl⟩
    cases a using Fin.cases with
    | zero => simpa using hs
    | succ a => simpa using (mem_rangeIn.1 hj) ⟨a, rfl⟩) hc
end GroundTheory.Arith.SchemeCoh
