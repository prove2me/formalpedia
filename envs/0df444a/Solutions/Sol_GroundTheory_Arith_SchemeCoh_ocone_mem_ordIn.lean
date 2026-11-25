-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ocone_mem_ordIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:09.580549+00:00
-- url     : https://prove2.me/submissions/19a4dfea-b2cc-4289-a5f7-5f5b63bc9acc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_map_mem_supported
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_strictMono_cons
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_mem_ordIn
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_lt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ocone_single_of_not_lt
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_minIdx_mem

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
theorem _root_.solution {n m : ℕ} (i : Fin (m + 1) → ι) {c : Chain ι n}
    (hc : c ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i))) :
    ocone (minIdx i) c ∈ Finsupp.supported ℤ ℤ (ordIn (Set.range i)) :=
  map_mem_supported _ (fun j hj z => by
    obtain ⟨hj1, hj2⟩ := mem_ordIn.1 hj
    by_cases hlt : minIdx i < j 0
    · rw [ocone_single_of_lt hlt]
      refine Finsupp.single_mem_supported ℤ z (mem_ordIn.2 ⟨strictMono_cons hj1 hlt, ?_⟩)
      rintro x ⟨a, rfl⟩
      cases a using Fin.cases with
      | zero => simpa using minIdx_mem i
      | succ a => simpa using hj2 ⟨a, rfl⟩
    · rw [ocone_single_of_not_lt hlt]
      exact Submodule.zero_mem _) hc
end GroundTheory.Arith.SchemeCoh
