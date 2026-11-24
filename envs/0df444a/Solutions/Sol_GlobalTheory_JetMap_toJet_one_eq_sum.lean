-- Prove2me | solution 1 for GlobalTheory.JetMap.toJet_one_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:23:22.105195+00:00
-- url     : https://prove2.me/submissions/831791ae-c187-4cbb-a5f3-967fe82c9ea4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ToJetOneEqSum

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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetMap
namespace GlobalTheory.JetMap
theorem _root_.solution {R : Type} [CommRing R] {κ : Type} [Fintype κ] (g : MvPowerSeries κ R)
    (hg : constantCoeff g = 0) :
    toJet 1 g = ∑ p, coeff (Finsupp.single p 1) g • zR (R := R) 1 p := by
  classical
  have h : truncTotal (1 + 1) g = ∑ p, coeff (Finsupp.single p 1) g • (MvPolynomial.X p : MvPolynomial κ R) := by
    ext e
    rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_X', smul_eq_mul, mul_ite, _root_.mul_one, mul_zero]
    by_cases he : ∃ p, Finsupp.single p 1 = e
    · obtain ⟨p, rfl⟩ := he
      rw [if_pos (by simp), Finset.sum_eq_single p (fun q _ hq => if_neg fun h =>
        hq (Finsupp.single_left_injective one_ne_zero h)) (by simp), if_pos rfl]
    · rw [Finset.sum_eq_zero fun p _ => if_neg fun h => he ⟨p, h⟩]
      split_ifs with hd
      · have h0 : e.degree = 0 := by
          by_contra h0
          have h1 : e.degree = 1 := by omega
          have : e ∈ Set.range (fun a : κ => Finsupp.single a 1) := by
            rw [Finsupp.range_single_one]; exact h1
          exact he this
        rw [(Finsupp.degree_eq_zero_iff e).1 h0]
        simpa using hg
      · rfl
  unfold toJet
  rw [h]
  exact (map_sum (Ideal.Quotient.mkₐ R _) _ _).trans
    (Finset.sum_congr rfl fun p _ => map_smul (Ideal.Quotient.mkₐ R _) _ _)
end GlobalTheory.JetMap
