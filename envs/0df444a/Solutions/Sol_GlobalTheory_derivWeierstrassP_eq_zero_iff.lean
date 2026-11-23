-- Prove2me | solution 1 for GlobalTheory.derivWeierstrassP_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:52.878804+00:00
-- url     : https://prove2.me/submissions/ee602afd-259d-4700-9ddb-ba3c2a1fb7e4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_sub_mem_lattice_of_weierstrassP_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ z + z ∈ L.lattice := by
  constructor
  · intro h
    simpa using sub_mem_lattice_of_weierstrassP_eq L (w := -z) hz (by simpa using hz)
      (by simp) (by simp [h])
  · intro h
    have := L.derivWeierstrassP_add_coe (-z) ⟨_, h⟩
    simpa [CharZero.eq_neg_self_iff] using this
end GlobalTheory
