-- Prove2me | solution 1 for GlobalTheory.HarmCopies.monomial_eq_boxSer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:12:08.352281+00:00
-- url     : https://prove2.me/submissions/2fb3f55e-6adb-4def-9777-a23501339919

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
theorem _root_.solution {k : Type} [CommRing k] {n d : ℕ} (e : Fin n × Fin d →₀ ℕ) :
    (MvPowerSeries.monomial e 1 : PS k n d) =
      boxSer fun b => ∏ j : Fin d, (MvPowerSeries.X ((0 : Fin 1), j) : PS k 1 d) ^ e (b, j) := by
  unfold boxSer
  simp only [map_prod, map_pow, MvPowerSeries.rename_X]
  rw [← Fintype.prod_prod_type' (fun b j => (MvPowerSeries.X (b, j) : PS k n d) ^ e (b, j)),
    MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
end GlobalTheory.HarmCopies
