-- Prove2me | solution 1 for GlobalTheory.JetSer.toJet_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:31.450583+00:00
-- url     : https://prove2.me/submissions/1793af3b-ed1a-48c9-92b8-0f1a8053dbdf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace GlobalTheory.JetSer
theorem _root_.solution {κ : Type} [Finite κ] (m : ℕ) (j : κ) : toJet m (X j : MvPowerSeries κ R) = zR m j := by
  classical
  unfold toJet
  rcases m with _ | m
  · have h : truncTotal (0 + 1) (X j : MvPowerSeries κ R) = 0 := by
      ext e
      rw [coeff_truncTotal_eq_ite]
      split_ifs with he
      · have : e = 0 := (Finsupp.degree_eq_zero_iff e).1 (by omega)
        subst this
        simp
      · simp
    rw [h, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.2 (by
      rw [zero_add, pow_one]; exact Ideal.subset_span ⟨j, rfl⟩)).symm
  · congr 1
    ext e
    rw [coeff_truncTotal_eq_ite, MvPowerSeries.coeff_X, MvPolynomial.coeff_X']
    by_cases h : e = Finsupp.single j 1
    · subst h
      simp
    · simp [h, Ne.symm h]
end GlobalTheory.JetSer
