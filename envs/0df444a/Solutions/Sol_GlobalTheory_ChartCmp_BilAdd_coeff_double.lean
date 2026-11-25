-- Prove2me | solution 1 for GlobalTheory.ChartCmp.BilAdd.coeff_double
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:36:02.082694+00:00
-- url     : https://prove2.me/submissions/1f0f22f6-4c06-430a-9568-a37ec048d2d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesJetEqCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetEqBilinearSeriesOfBiadditive

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
open GlobalTheory GlobalTheory.ChartCmp GlobalTheory.ChartCmp.BilAdd
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.ChartCmp.BilAdd
theorem _root_.solution (j : Fin 2) (g : PS k 2 d) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) =
      2 ^ degIn j e * MvPowerSeries.coeff e g := by
  have h : ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g =
      MvPowerSeries.rescale (fun p : Fin 2 × Fin d => if p.1 = j then (2 : k) else 1) g := by
    rw [MvPowerSeries.rescale_eq_subst]
    unfold ev
    congr 1
    funext p
    by_cases hp : p.1 = j
    · subst hp
      simp [pt, two_smul]
    · simp [hp, pt]
  rw [h, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, degIn, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp
end GlobalTheory.ChartCmp.BilAdd
