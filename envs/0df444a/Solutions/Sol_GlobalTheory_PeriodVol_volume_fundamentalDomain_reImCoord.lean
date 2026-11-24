-- Prove2me | solution 1 for GlobalTheory.PeriodVol.volume_fundamentalDomain_reImCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:35.831292+00:00
-- url     : https://prove2.me/submissions/12840131-8c12-4be0-8912-75247703a0c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_VolumeFundamentalDomainPeriodLattice
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_inl
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_inr
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_symm_re
import Theorems.Thm_GlobalTheory_PeriodVol_reImCoord_symm_im
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_inl
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_inr
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_symm_re
attribute [local simp] GlobalTheory.PeriodVol.reImCoord_symm_im

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodVol
namespace GlobalTheory.PeriodVol
theorem _root_.solution (g : ℕ) :
    volume (ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g))) = 1 := by
  have h : ZSpan.fundamentalDomain (Module.Basis.ofEquivFun (reImCoord g)) =
      Set.pi Set.univ fun _ : Fin g =>
        Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext z
    simp [ZSpan.fundamentalDomain, forall_and]
    tauto
  rw [h, volume_pi_pi]
  refine Finset.prod_eq_one fun _ _ => ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet]
  simp [Measure.volume_eq_prod]
end GlobalTheory.PeriodVol
