-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.derivWeierstrassP_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:59:00.158491+00:00
-- url     : https://prove2.me/submissions/b4476fae-5d3d-4ed7-93ad-9dfcc40f18ab

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_of_eventuallyEq_nhdsNE
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_comp_add
import Theorems.Thm_GroundTheory_Global_Elliptic_derivWeierstrassP_add
import Theorems.Thm_GroundTheory_Global_Elliptic_exists_continuousAt_chordSlope
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub


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
theorem _root_.solution {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘'[L] (2 * w) = -(tangentSlope L w * (℘[L] (2 * w) - ℘[L] w) + ℘'[L] w) := by
  obtain ⟨s, hs, hsw, hev⟩ := exists_continuousAt_chordSlope hw h2w
  have hww : w + w ∉ L.lattice := by rwa [← two_mul]
  have hc : ContinuousAt (fun z ↦ ℘'[L] (z + w)) w :=
    ((L.analyticOnNhd_derivWeierstrassP (w + w) hww).comp (g := ℘'[L]) (f := fun z ↦ z + w)
      (by fun_prop)).continuousAt
  have hc' : ContinuousAt (fun z ↦ ℘[L] (z + w)) w :=
    (analyticAt_weierstrassP_comp_add hww).continuousAt
  have hg : ContinuousAt (fun z ↦ -(s z * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z)) w :=
    ((hs.mul (hc'.sub (L.analyticOnNhd_weierstrassP w hw).continuousAt)).add
      (L.analyticOnNhd_derivWeierstrassP w hw).continuousAt).neg
  have := eq_of_eventuallyEq_nhdsNE hc hg (hev.mono fun z ⟨h1, h2, h3, h4⟩ ↦ by
    simp only
    rw [derivWeierstrassP_add h1 hw h2 h3, h4])
  simp only [hsw] at this
  rw [two_mul, this]
end GroundTheory.Global.Elliptic
