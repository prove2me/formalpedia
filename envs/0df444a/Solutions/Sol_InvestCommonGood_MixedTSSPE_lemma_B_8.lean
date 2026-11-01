-- Prove2me | solution 1 for InvestCommonGood.MixedTSSPE.lemma_B_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T15:35:31.12323+00:00
-- url     : https://prove2.me/submissions/624974b0-a0bc-4a68-b2b0-b88d128cecc2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvestCommonGood_MixedTSSPE_Conditions
import Theorems.Thm_InvestCommonGood_MixedTSSPE_lemma_B_8_ii
import Theorems.Thm_InvestCommonGood_MixedTSSPE_theorem_2

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
open VarContrib.RegularMPE
open InvestCommonGood.MixedTSSPE

theorem solution {Ω : Type*} [MeasurableSpace Ω] (m : Model) (S : Setting Ω) (c1 c2 zs xs θ z1 z2 xh q : ℝ)
    (hS : InvestCommonGood.MixedTSSPE.Standing m S) (hc2 : 0 < c2) (hc12 : c2 < c1) (hA1 : Assumption1 m S)
    (hA2 : Assumption2 m S zs) (hA4 : Assumption4 m S xs) (hA5 : Assumption5 m S c2 θ z2)
    (hxh : IsLemma2Point m S xh) (hq0 : 0 < q) (hq1 : q < 1)
    (hθ : θ < xh) (hz1 : xh < z1) (hz12 : z1 < z2)
    (hB21 : Jfun m S z1 - Jfun m S θ = c1) (hB22 : qB22 m S θ z1 z2 = q)
    (hB23 : B23 m S θ z1) :
    ∃ U1 V1 V2 : ℝ → ℝ, Sec42 m S ![c1, c2] θ ![z1, z2] q U1 V1 V2 ∧
      ∀ Rd : InvestCommonGood.MixedTSSPE.Rand Ω, RandStanding S Rd →
        IsSPE m S Rd ![c1, c2] θ q ![z1, z2] (rate29 m ![U1, V2] ![c1, c2] ![z1, z2] θ) := by
  have hF := lemma_B_8_ii m S c1 c2 zs xs θ z1 z2 xh q hS hc2 hc12 hA1 hA2 hA4 hA5 hxh hq0 hq1
    hθ hz1 hz12 hB21 hB22 hB23
  refine ⟨_, _, _, hF, ?_⟩
  exact theorem_2 m S zs θ q ![c1, c2] ![z1, z2] _ _ _ hS hA1 hA2 (by simpa using hc2)
    (by simpa using hc12) hq0 hq1 hF
