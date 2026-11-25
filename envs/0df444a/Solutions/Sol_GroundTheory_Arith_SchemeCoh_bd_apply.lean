-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:09.382441+00:00
-- url     : https://prove2.me/submissions/dd475f31-4fc3-4900-9829-5fd1b5331666

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hom_finset_sum_apply


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
theorem _root_.solution (n : ℕ) (c : Chain ι (n + 1)) :
    bd n c = ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • chainMap k.succAbove c := by
  have h := hom_finset_sum_apply Finset.univ
    (fun k : Fin (n + 2) => ((-1 : ℤ) ^ (k : ℕ)) • (chainSimplicial ι).δ k) c
  refine h.trans (Finset.sum_congr rfl fun k _ => ?_)
  rfl
end GroundTheory.Arith.SchemeCoh
