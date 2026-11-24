-- Prove2me | solution 1 for GlobalTheory.AnArc.tate_isConvLine_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:43.814177+00:00
-- url     : https://prove2.me/submissions/166e6910-835f-4147-b074-e9ee8b67b2b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (τ₀ : ℂ) (T₀ : ℝ) : (tate τ₀).IsConvLine T₀ ↔ -τ₀.im / 2 ≤ T₀ := by
  have key : ∀ μ : ℤ, (((tate τ₀).H ((tate τ₀).ct μ) ((tate τ₀).ct μ)).re / 2 - ((tate τ₀).T μ μ).im ≤
      T₀ * (tate τ₀).be μ μ) ↔ -(τ₀.im * μ * μ) ≤ T₀ * (2 * μ * μ) := fun μ => by
    change (hermForm (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 0).re / 2 - (TInt τ₀ μ μ).im ≤ T₀ * (beInt μ μ : ℤ) ↔ _
    simp [hermForm]
  constructor
  · intro h
    have := (key 1).1 (h (1 : ℤ))
    simp only [Int.cast_one, mul_one] at this
    linarith
  · intro h μ
    refine (key μ).2 ?_
    nlinarith [mul_self_nonneg ((show ℤ from μ) : ℝ)]
end GlobalTheory.AnArc
