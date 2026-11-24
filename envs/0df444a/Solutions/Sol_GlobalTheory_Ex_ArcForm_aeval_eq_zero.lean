-- Prove2me | solution 1 for GlobalTheory.Ex.ArcForm.aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:42:51.170052+00:00
-- url     : https://prove2.me/submissions/6e9257d4-aae1-4434-b995-d6a62fa2c848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AevalArcTxEqZero
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
import Theorems.Thm_GlobalTheory_Conv_coe_expandConvLaurent
import Theorems.Thm_GlobalTheory_Conv_expandConv_u
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv
attribute [local simp] GlobalTheory.Conv.coe_expandConvLaurent
attribute [local simp] GlobalTheory.Conv.expandConv_u



set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.ArcForm
namespace GlobalTheory.Ex.ArcForm
theorem _root_.solution {ι : Type} (f : ι → PowerSeries ℂ) (F : MvPolynomial ι ℂ) {ε : ℝ} (hε : 0 < ε)
    (v : ℂˣ → ι → ℂ) (hs : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → ∀ i,
      HasSum (fun n => PowerSeries.coeff n (f i) * (u : ℂ) ^ n) (v u i))
    (hF : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → MvPolynomial.eval (v u) F = 0) : MvPolynomial.aeval f F = 0 := by
  have hmem : ∀ i, f i ∈ GlobalTheory.Conv.discSeries ε := fun i u hu => by
    rcases eq_or_ne u 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (hs (Units.mk0 u h0) hu i).summable
  set G : GlobalTheory.Conv.discSeries ε := MvPolynomial.aeval (fun i => (⟨f i, hmem i⟩ : GlobalTheory.Conv.discSeries ε)) F with hG
  have hGv : (G : PowerSeries ℂ) = MvPolynomial.aeval f F :=
    MvPolynomial.comp_aeval_apply _ (GlobalTheory.Conv.discSeries ε).val F
  rw [← hGv]
  refine GlobalTheory.Conv.eq_zero_of_frequently_sum_eq_zero (GlobalTheory.Conv.discSeries_le_convSeries hε G.2)
    (Filter.Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hε)] with u h0 hu
  have h0' : u ≠ 0 := h0
  have hu' : ‖u‖ < ε := by simpa using hu
  rw [← GlobalTheory.Conv.evalDisc_apply hu', hG, MvPolynomial.comp_aeval_apply, ← hF (Units.mk0 u h0') hu',
    MvPolynomial.aeval_eq_eval]
  congr 2
  funext i
  exact (hs (Units.mk0 u h0') hu' i).tsum_eq
end GlobalTheory.Ex.ArcForm
