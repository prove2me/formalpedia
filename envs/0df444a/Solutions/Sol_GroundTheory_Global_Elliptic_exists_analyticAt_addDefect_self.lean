-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_analyticAt_addDefect_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:56:38.724267+00:00
-- url     : https://prove2.me/submissions/eaa375b6-1ee7-4bc2-89aa-5851772dc757

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_comp_add
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_dslope
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero


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
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H w ∧ addDefect L w =ᶠ[𝓝[≠] w] H := by
  have hpw : AnalyticAt ℂ ℘[L] w := L.analyticOnNhd_weierstrassP w hw
  have hdw : AnalyticAt ℂ ℘'[L] w := L.analyticOnNhd_derivWeierstrassP w hw
  have h1 := analyticAt_dslope hpw
  have h2 := analyticAt_dslope hdw
  have hne : dslope ℘[L] w w ≠ 0 := by
    rw [dslope_same, L.deriv_weierstrassP]
    exact fun h ↦ h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  have hW := analyticAt_weierstrassP_comp_add (L := L) (x := w) (w := w) (by rwa [← two_mul])
  refine ⟨fun z ↦ ℘[L] (z + w) + ℘[L] z + ℘[L] w -
    (dslope ℘'[L] w z / dslope ℘[L] w z) ^ 2 / 4, ?_, ?_⟩
  · apply AnalyticAt.sub (by fun_prop)
    exact ((h2.div h1 hne).pow 2).div analyticAt_const (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [addDefect, chordSlope]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      div_div_div_cancel_right₀ (sub_ne_zero.2 hz)]
end GroundTheory.Global.Elliptic
