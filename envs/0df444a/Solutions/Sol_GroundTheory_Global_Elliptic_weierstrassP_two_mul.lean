-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassP_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:56:21.20225+00:00
-- url     : https://prove2.me/submissions/60dbed59-3b4e-4aa7-bf50-786e82d5f212

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_of_eventuallyEq_nhdsNE
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_comp_add
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_add
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
    ℘[L] (2 * w) = tangentSlope L w ^ 2 / 4 - 2 * ℘[L] w := by
  obtain ⟨s, hs, hsw, hev⟩ := exists_continuousAt_chordSlope hw h2w
  have hc : ContinuousAt (fun z ↦ ℘[L] (z + w)) w :=
    (analyticAt_weierstrassP_comp_add (show w + w ∉ L.lattice by rwa [← two_mul])).continuousAt
  have hg : ContinuousAt (fun z ↦ s z ^ 2 / 4 - ℘[L] z - ℘[L] w) w :=
    (((hs.pow 2).div_const 4).sub (L.analyticOnNhd_weierstrassP w hw).continuousAt).sub
      continuousAt_const
  have := eq_of_eventuallyEq_nhdsNE hc hg (hev.mono fun z ⟨h1, h2, h3, h4⟩ ↦ by
    simp only
    rw [weierstrassP_add h1 hw h2 h3, h4])
  simp only [hsw] at this
  rw [two_mul, this]
  ring
end GroundTheory.Global.Elliptic
