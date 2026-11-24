-- Prove2me | solution 1 for GlobalTheory.FourierChainCompare.coeff_chr_of_inversion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:09:41.824003+00:00
-- url     : https://prove2.me/submissions/0c9a531b-5326-4b45-b4d4-2f9d39cb8006

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_FormalGroupLawCompMulNZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_EqZeroOrSingleOfDegreeLtTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_AddCharMemValuationSubring
import Theorems.Thm_GlobalTheory_FourierChainCompare_chr_apply
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_X
import Theorems.Thm_GlobalTheory_FormalSeries_jacobian_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one
attribute [local simp] GlobalTheory.FormalSeries.jacobian_X
attribute [local simp] GlobalTheory.FormalSeries.jacobian_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
open GlobalTheory GlobalTheory.FourierChainCompare
variable {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K] [Fintype A] [Fintype B]
namespace GlobalTheory.FourierChainCompare
theorem _root_.solution [DecidableEq B] {e : A → B → Kˣ} (he : IsPerfectPairing e) (t₀ : B)
    (h : ∀ a, ((e a t₀ : Kˣ) : K) =
      ∑ t : B, IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t * ((e a t : Kˣ) : K)) (t : B) :
    IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t = if t = t₀ then 1 else 0 := by
  have li := Fintype.linearIndependent_iff.mp
    ((linearIndependent_addChar A K).comp _ (chr_injective he))
    (fun t => IndefiniteRowSideFullHecke.PerfectPairings.fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t - if t = t₀ then 1 else 0)
    (by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, chr_apply, smul_eq_mul,
        sub_mul, Finset.sum_sub_distrib, ← h a]
      simp)
  exact sub_eq_zero.mp (li t)
end GlobalTheory.FourierChainCompare
