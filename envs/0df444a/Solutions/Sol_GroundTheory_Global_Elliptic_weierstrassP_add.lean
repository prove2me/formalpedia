-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassP_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:41:40.723346+00:00
-- url     : https://prove2.me/submissions/50df01b2-25ef-4488-8746-184b8418fa3d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_chordSlope_comm
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_add_of_two_mul_notMem
import Theorems.Thm_GroundTheory_Global_Elliptic_add_add_eq_zero_of_roots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  by_cases h2w : 2 * w ∈ L.lattice
  · by_cases h2z : 2 * z ∈ L.lattice
    · have d1 := derivWeierstrassP_eq_zero_of_two_mul_mem h2z
      have d2 := derivWeierstrassP_eq_zero_of_two_mul_mem h2w
      have root : ∀ u ∉ L.lattice, 2 * u ∈ L.lattice →
          4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := fun u hu h2 ↦ by
        rw [← L.derivWeierstrassP_sq u hu, derivWeierstrassP_eq_zero_of_two_mul_mem h2]
        ring
      have hne : ∀ {a b : ℂ}, a ∉ L.lattice → b ∉ L.lattice → a - b ∉ L.lattice →
          a + b ∉ L.lattice → ℘[L] a ≠ ℘[L] b := fun ha hb h1 h2 h ↦
        (sub_mem_or_add_mem_of_weierstrassP_eq ha hb h).elim h1 h2
      have nz : -z ∉ L.lattice := fun h ↦ hz (by simpa using neg_mem h)
      have nw : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
      have a1 : z - (z + w) ∉ L.lattice := by rwa [show z - (z + w) = -w by ring]
      have a2 : z + (z + w) ∉ L.lattice := fun h ↦ hw (by
        have := sub_mem h h2z
        rwa [show z + (z + w) - 2 * z = w by ring] at this)
      have a3 : w - (z + w) ∉ L.lattice := by rwa [show w - (z + w) = -z by ring]
      have a4 : w + (z + w) ∉ L.lattice := fun h ↦ hz (by
        have := sub_mem h h2w
        rwa [show w + (z + w) - 2 * w = z by ring] at this)
      have hs := add_add_eq_zero_of_roots (hne hz hw hzw hzw') (hne hz hzw' a1 a2)
        (hne hw hzw' a3 a4) (root z hz h2z) (root w hw h2w)
        (root _ hzw' (by rw [mul_add]; exact add_mem h2z h2w))
      rw [chordSlope, d1, d2, sub_self, zero_div]
      linear_combination hs
    · have hwz : w - z ∉ L.lattice := fun h ↦ hzw (by simpa using neg_mem h)
      have := weierstrassP_add_of_two_mul_notMem hz h2z hw hwz (by rwa [add_comm])
      rw [add_comm, chordSlope_comm] at this
      linear_combination this
  · exact weierstrassP_add_of_two_mul_notMem hw h2w hz hzw hzw'
end GroundTheory.Global.Elliptic
