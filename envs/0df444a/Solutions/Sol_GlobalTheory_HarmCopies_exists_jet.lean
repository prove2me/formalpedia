-- Prove2me | solution 1 for GlobalTheory.HarmCopies.exists_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:06:31.583651+00:00
-- url     : https://prove2.me/submissions/50257c31-cedb-4561-9721-6d7e8381806b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeIndependenceHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_HarmonicValueCopiesGaugeIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.HarmCopies
open GlobalTheory.PowGerm
namespace GlobalTheory.HarmCopies
theorem _root_.solution {k : Type} [CommRing k] {n d : ℕ} (N : ℕ) (f : PS k n d) :
    ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ N →
      MvPowerSeries.coeff e f =
        MvPowerSeries.coeff e (∑ j : S, MvPowerSeries.coeff j.1 f • (MvPowerSeries.monomial j.1 1 : PS k n d)) := by
  classical
  refine ⟨(Finsupp.finite_of_degree_le N).toFinset, fun e he => ?_⟩
  rw [map_sum, Finset.sum_eq_single ⟨e, by simpa using he⟩]
  · simp
  · intro j _ hj
    rw [map_smul, MvPowerSeries.coeff_monomial_ne (fun h => hj (Subtype.ext h.symm)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end GlobalTheory.HarmCopies
