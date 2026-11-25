-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_analyticAt_addDefect_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:09:36.910612+00:00
-- url     : https://prove2.me/submissions/c1d93734-60ae-4923-bc04-572e03c43ab2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_eq_except_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_derivWeierstrassP_eq_except_zero
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_comp_add
import Theorems.Thm_GroundTheory_Global_Elliptic_addDefect_algebra_zero

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
theorem _root_.solution {w : ℂ} (hw : w ∉ L.lattice) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 0 ∧ addDefect L w =ᶠ[𝓝[≠] 0] H := by
  have hP : AnalyticAt ℂ ℘[L - (0 : ℂ)] 0 := L.analyticAt_weierstrassPExcept 0
  have hP' : AnalyticAt ℂ ℘'[L - (0 : ℂ)] 0 := L.analyticAt_derivWeierstrassPExcept 0
  have hW : AnalyticAt ℂ (fun z ↦ ℘[L] (z + w)) 0 :=
    analyticAt_weierstrassP_comp_add (by simpa using hw)
  have hBf : AnalyticAt ℂ (fun z ↦ z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 1) 0 := by fun_prop
  have hBf0 : (fun z ↦ z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 1) 0 ≠ 0 := by simp
  refine ⟨fun z ↦ ℘[L] (z + w) + ℘[L] w + ℘[L - (0 : ℂ)] z +
      (8 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 4 * z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) ^ 2 -
        z ^ 4 * (℘'[L - (0 : ℂ)] z - ℘'[L] w) ^ 2 + 4 * z * (℘'[L - (0 : ℂ)] z - ℘'[L] w)) /
      (4 * (z ^ 2 * (℘[L - (0 : ℂ)] z - ℘[L] w) + 1) ^ 2), ?_, ?_, ?_⟩
  · refine AnalyticAt.add (by fun_prop) (AnalyticAt.div (by fun_prop) (by fun_prop) ?_)
    simp
  · simp
    ring
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (hBf.continuousAt.eventually_ne hBf0)] with z hz hBz
    have hz : z ≠ 0 := hz
    have e1 := weierstrassP_eq_except_zero (L := L) z
    have e2 := derivWeierstrassP_eq_except_zero (L := L) z
    simp only [addDefect, chordSlope]
    rw [e2, e1]
    exact addDefect_algebra_zero _ _ _ _ _ _ hz hBz
end GroundTheory.Global.Elliptic
