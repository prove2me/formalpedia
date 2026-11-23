-- Prove2me | solution 1 for GlobalTheory.weierstrassP_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:53.068267+00:00
-- url     : https://prove2.me/submissions/ea3229a2-9677-4933-9a09-0f506d8a88fc

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
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    ℘[L] z = ℘[L] w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  constructor
  · intro h
    have h1 : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 := by
      rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
    · exact .inl (sub_mem_lattice_of_weierstrassP_eq L hz hw h h2)
    · exact .inr (by
        simpa using sub_mem_lattice_of_weierstrassP_eq L (w := -w) hz (by simpa using hw)
          (by simpa using h) (by simpa using h2))
  · rintro (h | h)
    · rw [← L.weierstrassP_add_coe w ⟨_, h⟩]; simp
    · rw [← L.weierstrassP_neg w, ← L.weierstrassP_add_coe (-w) ⟨_, h⟩]; simp
end GlobalTheory
