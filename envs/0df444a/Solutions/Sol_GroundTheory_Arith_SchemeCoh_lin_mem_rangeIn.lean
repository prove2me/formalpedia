-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.lin_mem_rangeIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:47:09.716698+00:00
-- url     : https://prove2.me/submissions/3a8be351-3ffb-456c-9dba-01b480c9eba5

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_lin_single
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
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
theorem _root_.solution {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) {S : Set ι}
    (hf : ∀ j : Fin (m + 1) → ι, Set.range j ⊆ S →
      f j ∈ Finsupp.supported ℤ ℤ (rangeIn (n := n) (Set.range j)))
    {c : Chain ι m} (hc : c ∈ Finsupp.supported ℤ ℤ (rangeIn S)) :
    lin f c ∈ Finsupp.supported ℤ ℤ (rangeIn S) :=
  map_mem_supported _ (fun j hj z => by
    rw [lin_single]
    exact Submodule.smul_mem _ z (Finsupp.supported_mono
      (fun k hk => mem_rangeIn.2 ((mem_rangeIn.1 hk).trans (mem_rangeIn.1 hj))) (hf j hj))) hc
end GroundTheory.Arith.SchemeCoh
