-- Prove2me | solution 1 for GlobalTheory.AnVal.JetCorr.jet_point_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:50:30.614233+00:00
-- url     : https://prove2.me/submissions/5dff28d9-9f59-464b-a4a9-020213261756

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CorrOfJetsOfAnalyticFrameProducts

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetCorr
namespace GlobalTheory.AnVal.JetCorr
theorem _root_.solution {K : Type} [Field K] {J : Type} {m : ℕ} (p : PrimeSpectrum (Jet K J m)) :
    p = IsLocalRing.closedPoint (Jet K J m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hn := jet_nilpotent_of_orig K J m (sub_const_mem_orig (R := K) q)
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      refine (IsLocalRing.mem_maximalIdeal _).mp ha ?_
      have e : algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) =
          Ideal.Quotient.mk (orig K J ^ (m + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [← MvPolynomial.algebraMap_eq]; rfl
      have hsplit : Ideal.Quotient.mk (orig K J ^ (m + 1)) q =
          algebraMap K (Jet K J m) (MvPolynomial.constantCoeff q) +
            Ideal.Quotient.mk (orig K J ^ (m + 1)) (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) := by
        rw [map_sub, e, add_sub_cancel]
      rw [hsplit]
      exact IsNilpotent.isUnit_add_left_of_commute hn
        ((isUnit_iff_ne_zero.mpr hne).map (algebraMap K (Jet K J m))) (Commute.all _ _)
    rwa [h0, map_zero, sub_zero] at hn
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
end GlobalTheory.AnVal.JetCorr
