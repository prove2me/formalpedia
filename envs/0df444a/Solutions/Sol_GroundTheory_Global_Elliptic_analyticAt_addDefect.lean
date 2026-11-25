-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.analyticAt_addDefect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:09.766492+00:00
-- url     : https://prove2.me/submissions/aa0a6747-c8d5-4160-bdd7-aa848522964a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_comp_add
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
theorem _root_.solution {w z : ℂ} (hw : w ∉ L.lattice) (hz : z ∉ L.lattice)
    (hzw : z - w ∉ L.lattice) (hzw' : z + w ∉ L.lattice) : AnalyticAt ℂ (addDefect L w) z := by
  have hne : ℘[L] z - ℘[L] w ≠ 0 := fun h ↦ by
    rcases sub_mem_or_add_mem_of_weierstrassP_eq hz hw (sub_eq_zero.1 h) with h' | h'
    · exact hzw h'
    · exact hzw' h'
  have h1 := analyticAt_weierstrassP_comp_add hzw'
  have h2 := L.analyticOnNhd_weierstrassP z hz
  have h3 := L.analyticOnNhd_derivWeierstrassP z hz
  unfold addDefect chordSlope
  apply AnalyticAt.sub (by fun_prop)
  apply AnalyticAt.div _ analyticAt_const (by norm_num)
  apply AnalyticAt.pow
  exact AnalyticAt.div (by fun_prop) (by fun_prop) hne
end GroundTheory.Global.Elliptic
