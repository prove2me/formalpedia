-- Prove2me | solution 1 for GlobalTheory.Conv.isHolTo_halfCurve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:35.257669+00:00
-- url     : https://prove2.me/submissions/1b9ff847-8d70-46fd-a8e4-6dd9bcb72782

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
import Theorems.Thm_GlobalTheory_Conv_halfCurve_comp
import Theorems.Thm_P2M_GlobalTheory_Conv_valAt__halfCurve_ca595a84c520
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_differentiableOn_of_eq_ev
import Theorems.Thm_GlobalTheory_Conv_evLoc_algebraMap
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_affine
import Theorems.Thm_GlobalTheory_HolHom_isHolTo_of_holAt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.evLoc_algebraMap
attribute [local simp] GlobalTheory.Conv.expandConv_u



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {Z : Scheme.{0}}
namespace GlobalTheory.Conv
theorem _root_.solution {T : ℝ} (yT : Sp (halfRing T) ⟶ Z) :
    IsHolTo {w : ℂ | T < w.im} (halfCurve yT) := by
  have ho : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  refine isHolTo_of_holAt ho fun z hz => ?_
  have h : HolAt (halfCurve (𝟙 (Sp (halfRing T)))) z := by
    refine holAt_of_affine (isAffineOpen_top _) le_top (Eventually.of_forall fun _ => le_top)
      fun g => ?_
    exact (differentiableOn_of_eq_ev (valR (𝟙 (Sp (halfRing T))) ⊤ g)
      fun w hw => (valAt'_halfCurve (𝟙 _) le_top hw).2 g).differentiableAt (ho.mem_nhds hz)
  have := h.comp yT
  simpa only [← halfCurve_comp, Category.id_comp] using this
end GlobalTheory.Conv
