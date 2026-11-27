-- Prove2me | solution 1 for GlobalTheory.AnValJetEx.jet_point_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:23.693327+00:00
-- url     : https://prove2.me/submissions/c54c1c7b-b0e4-49fd-8678-1ca28a9126b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isUnit_of_jetAug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_mk


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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnValJetEx
theorem _root_.solution {K : Type} [Field K] {I : Type} {m : ℕ} (p : PrimeSpectrum (Jet K I m)) :
    p = IsLocalRing.closedPoint (Jet K I m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K I m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
end GlobalTheory.AnValJetEx
