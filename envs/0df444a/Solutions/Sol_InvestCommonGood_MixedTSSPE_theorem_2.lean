-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:35:31.876453+00:00
-- url     : https://prove2.me/submissions/f3b4837d-a939-4137-9824-c7f7264038b2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_6
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_7

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (zs θ q : ℝ) (c z : Fin 2 → ℝ) (U1 V1 V2 : ℝ → ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hA1 : Assumption1 m S) (hA2 : Assumption2 m S zs)
    (hc : 0 < c 1) (hc12 : c 1 < c 0) (hq0 : 0 < q) (hq1 : q < 1)
    (hF : Sec42 m S c θ z q U1 V1 V2) :
    ∀ Rd : InvestCommonGood.MixedTSSPE.Rand Ω, RandStanding S Rd →
      IsSPE m S Rd c θ q z (rate29 m ![U1, V2] c z θ) := by
  intro Rd hRd
  exact lemma_B_6 m S zs θ q c z U1 V1 V2 hS hA1 hA2 hc hc12 hq0 hq1 hF Rd hRd
    (lemma_B_7 m S zs θ q c z U1 V1 V2 hS hA1 hA2 hc hc12 hq0 hq1 hF Rd hRd)
