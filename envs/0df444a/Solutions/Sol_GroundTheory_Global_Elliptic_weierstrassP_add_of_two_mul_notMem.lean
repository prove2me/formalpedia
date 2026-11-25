-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassP_add_of_two_mul_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:47.053568+00:00
-- url     : https://prove2.me/submissions/68df09c7-f6c6-4b78-8cd2-95c7a36887c2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_meromorphicOrderAt_nonneg_of_simple_pole
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_of_eventuallyEq_nhdsNE
import Theorems.Thm_GroundTheory_Global_Elliptic_isEllipticFunction_addDefect
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_addDefect
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_analyticAt_addDefect_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_analyticAt_addDefect_self
import Theorems.Thm_GroundTheory_Global_Elliptic_neg_one_le_meromorphicOrderAt_addDefect_neg
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_meromorphicOrderAt_add
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_const_of_meromorphicOrderAt_nonneg


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
theorem _root_.solution {z w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) (hz : z ∉ L.lattice) (hzw : z - w ∉ L.lattice)
    (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
  have hE := isEllipticFunction_addDefect (L := L) w
  have hw' : -w ∉ L.lattice := fun h ↦ hw (by simpa using neg_mem h)
  have ho : ∀ u, 0 ≤ meromorphicOrderAt (addDefect L w) u := by
    apply meromorphicOrderAt_nonneg_of_simple_pole hE
      (neg_one_le_meromorphicOrderAt_addDefect_neg hw h2w)
    intro u hu
    by_cases hu0 : u ∈ L.lattice
    · have := hE.2.meromorphicOrderAt_add hu0 0
      rw [zero_add] at this
      rw [this]
      obtain ⟨H, hH, -, hev⟩ := exists_analyticAt_addDefect_zero hw
      rw [meromorphicOrderAt_congr hev]
      exact hH.meromorphicOrderAt_nonneg
    by_cases hu1 : u - w ∈ L.lattice
    · have := hE.2.meromorphicOrderAt_add hu1 w
      rw [add_sub_cancel] at this
      rw [this]
      obtain ⟨H, hH, hev⟩ := exists_analyticAt_addDefect_self hw h2w
      rw [meromorphicOrderAt_congr hev]
      exact hH.meromorphicOrderAt_nonneg
    · exact (analyticAt_addDefect hw hu0 hu1
        (by rwa [sub_neg_eq_add] at hu)).meromorphicOrderAt_nonneg
  obtain ⟨c, hc⟩ := exists_const_of_meromorphicOrderAt_nonneg L hE.1 hE.2 ho
  obtain ⟨H, hH, hH0, hev⟩ := exists_analyticAt_addDefect_zero (L := L) hw
  have hc0 : c = 0 := by
    have hgen : ∀ᶠ u in 𝓝[≠] (0 : ℂ), addDefect L w u = c := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
        nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
          (continuous_sub_right w)).mem_nhds (by simpa using hw')),
        nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
          (continuous_add_right w)).mem_nhds (by simpa using hw))] with u hu0 hu1 hu2 hu3
      exact hc u (analyticAt_addDefect hw (fun h ↦ hu1 ⟨h, hu0⟩) hu2 hu3)
    have := eq_of_eventuallyEq_nhdsNE hH.continuousAt continuousAt_const (hev.symm.trans hgen)
    rw [← this, hH0]
  have := hc z (analyticAt_addDefect hw hz hzw hzw')
  rw [hc0] at this
  simp only [addDefect] at this
  linear_combination this
end GroundTheory.Global.Elliptic
