-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_continuousAt_chordSlope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:23.512005+00:00
-- url     : https://prove2.me/submissions/db5c4c66-243c-4dda-a74e-04334b1c2596

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Theorems.Thm_GroundTheory_Global_Elliptic_deriv_derivWeierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_dslope
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
    ∃ s : ℂ → ℂ, ContinuousAt s w ∧ s w = tangentSlope L w ∧
      ∀ᶠ z in 𝓝[≠] w, z ∉ L.lattice ∧ z - w ∉ L.lattice ∧ z + w ∉ L.lattice ∧
        chordSlope L z w = s z := by
  have hpw : AnalyticAt ℂ ℘[L] w := L.analyticOnNhd_weierstrassP w hw
  have hdw : AnalyticAt ℂ ℘'[L] w := L.analyticOnNhd_derivWeierstrassP w hw
  have hne : dslope ℘[L] w w ≠ 0 := by
    rw [dslope_same, L.deriv_weierstrassP]
    exact fun h ↦ h2w ((two_mul_mem_lattice_iff_derivWeierstrassP_eq_zero hw).2 h)
  refine ⟨fun z ↦ dslope ℘'[L] w z / dslope ℘[L] w z,
    ((analyticAt_dslope hdw).div (analyticAt_dslope hpw) hne).continuousAt, ?_, ?_⟩
  · simp only [dslope_same, L.deriv_weierstrassP, deriv_derivWeierstrassP hw, tangentSlope]
  · have h0 : (↑L.lattice \ {(0 : ℂ)})ᶜ ∈ 𝓝 (w - w) := by
      rw [sub_self]
      exact L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hw),
      nhdsWithin_le_nhds ((continuous_sub_right w).continuousAt.preimage_mem_nhds h0),
      nhdsWithin_le_nhds ((L.isClosed_lattice.isOpen_compl.preimage
        (continuous_add_right w)).mem_nhds (show w + w ∉ L.lattice by rwa [← two_mul]))]
      with z hz h1 h2 h3
    have hz' : z - w ≠ 0 := sub_ne_zero.2 hz
    refine ⟨h1, fun h ↦ h2 ⟨h, hz'⟩, h3, ?_⟩
    simp only [chordSlope]
    rw [dslope_of_ne _ hz, dslope_of_ne _ hz, slope_def_field, slope_def_field,
      div_div_div_cancel_right₀ hz']
end GroundTheory.Global.Elliptic
