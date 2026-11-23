-- Prove2me | solution 1 for GlobalTheory.ChartJLaw.psJet_eq_toJet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:24.935213+00:00
-- url     : https://prove2.me/submissions/4313662e-84a8-451b-92fd-f772933c051e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Theorems.Thm_GlobalTheory_JetSer_toJet_eq_mk_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ChartJLaw
variable {T : Type} [CommRing T] {d : ℕ}
namespace GlobalTheory.ChartJLaw
theorem _root_.solution {n : ℕ} (m : ℕ) (f : PS T n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    psJet m f = JetSer.toJet m f := by
  symm
  refine (JetSer.toJet_eq_mk_iff m f _).2 fun e he => ?_
  rw [MvPowerSeries.coeff_trunc]
  split_ifs with hlt
  · rfl
  · have hle : e ≤ Finsupp.equivFunOnFinite.symm fun _ => m + 1 := fun i => by
      have := Finsupp.le_degree i e
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      omega
    have heq : e = Finsupp.equivFunOnFinite.symm fun _ => m + 1 := by
      by_contra h
      exact hlt (lt_of_le_of_ne hle h)
    have h0 : e = 0 := by
      ext i
      exfalso
      have h1 := Finsupp.le_degree i e
      have h2 : e i = m + 1 := by rw [heq]; simp
      omega
    rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
end GlobalTheory.ChartJLaw
