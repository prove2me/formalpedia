-- Prove2me | solution 1 for GlobalTheory.FormalConnection.vf_vf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:11:47.79302+00:00
-- url     : https://prove2.me/submissions/13cd8f84-e5f3-4c05-880f-3415f46ea072

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalEvSecondPointOfXZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.FormalLog
open GlobalTheory GlobalTheory.FormalConnection
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]
namespace GlobalTheory.FormalConnection
theorem _root_.solution (c c' : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) :
    vf c (vf c' G) = vf (fun t => vf c (c' t)) G + ∑ s, ∑ t, c s * c' t * pderiv k s (pderiv k t G) := by
  have hL : vf c (vf c' G) = ∑ s, ∑ t, (c s * c' t * pderiv k s (pderiv k t G) +
      c s * pderiv k s (c' t) * pderiv k t G) := by
    simp only [vf, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  have hR : vf (fun t => vf c (c' t)) G = ∑ s, ∑ t, c s * pderiv k s (c' t) * pderiv k t G := by
    simp only [vf, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hL, hR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring
end GlobalTheory.FormalConnection
