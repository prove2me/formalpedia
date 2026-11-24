-- Prove2me | solution 1 for GlobalTheory.PrCompactOpen.eq_one_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:13.692665+00:00
-- url     : https://prove2.me/submissions/6371c3af-3043-4920-b0cb-249a4794f574

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsCOPrXCgrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.PrCompactOpen
namespace GlobalTheory.PrCompactOpen
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] (f : G → ℝ)
    (hc : Continuous f) (hm : ∀ x y, f (x * y) = f x * f y) (hp : ∀ x, 0 < f x)
    {P : Subgroup G} (hP : IsCompact (P : Set G)) {g : G} (hg : g ∈ P) : f g = 1 := by
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hm, one_mul]
    exact mul_left_cancel₀ (hp 1).ne' e
  have hpow : ∀ x : G, ∀ m : ℕ, f (x ^ m) = f x ^ m := by
    intro x m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih, pow_succ]
  obtain ⟨B, hB⟩ := (hP.image hc).bddAbove
  have hle : ∀ x ∈ P, f x ≤ 1 := by
    intro x hx
    by_contra hlt
    have hlt := not_le.mp hlt
    obtain ⟨m, hm'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlt).eventually_gt_atTop B).exists
    have : f (x ^ m) ≤ B := hB ⟨x ^ m, P.pow_mem hx m, rfl⟩
    rw [hpow] at this
    linarith
  have hprod : f g * f g⁻¹ = 1 := by rw [← hm, mul_inv_cancel, h1]
  have a := hle g hg
  have b := hle g⁻¹ (P.inv_mem hg)
  nlinarith [mul_le_mul_of_nonneg_left b (hp g).le, hp g⁻¹]
end GlobalTheory.PrCompactOpen
