-- Prove2me | solution 1 for GlobalTheory.QuotIntFJ.integral_rotate_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:47.449794+00:00
-- url     : https://prove2.me/submissions/e6be8e09-df40-4648-bbf9-71638370437c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ProperTripleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.QuotIntFJ
namespace GlobalTheory.QuotIntFJ
theorem _root_.solution {B X U : Type} [MeasurableSpace X] [MeasurableSpace B] [MeasurableSpace U]
    (β : Measure B) (μ : Measure X) (ρ : Measure U) [SFinite μ] [SFinite β] [SFinite ρ]
    (Φ : B → X → U → ℂ) (hΦ : Integrable (fun z : B × (X × U) => Φ z.1 z.2.1 z.2.2) (β.prod (μ.prod ρ))) :
    Integrable (fun b => ∫ x, ∫ u, Φ b x u ∂ρ ∂μ) β ∧
      ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ := by
  have hsec : ∀ᵐ b ∂β, Integrable (fun y : X × U => Φ b y.1 y.2) (μ.prod ρ) := hΦ.prod_right_ae
  have hin : ∀ᵐ b ∂β, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ = ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) := by
    filter_upwards [hsec] with b hb
    exact (integral_prod (fun y : X × U => Φ b y.1 y.2) hb).symm
  have hsw : Integrable (fun w : (X × U) × B => Φ w.2 w.1.1 w.1.2) ((μ.prod ρ).prod β) := hΦ.swap
  refine ⟨hΦ.integral_prod_left.congr (hin.mono fun b hb => hb.symm), ?_⟩
  calc ∫ b, ∫ x, ∫ u, Φ b x u ∂ρ ∂μ ∂β
      = ∫ b, ∫ y : X × U, Φ b y.1 y.2 ∂(μ.prod ρ) ∂β := integral_congr_ae hin
    _ = ∫ w : B × (X × U), Φ w.1 w.2.1 w.2.2 ∂(β.prod (μ.prod ρ)) := (integral_prod _ hΦ).symm
    _ = ∫ w : (X × U) × B, Φ w.2 w.1.1 w.1.2 ∂((μ.prod ρ).prod β) :=
        (integral_prod_swap (fun w : B × (X × U) => Φ w.1 w.2.1 w.2.2)).symm
    _ = ∫ y : X × U, ∫ b, Φ b y.1 y.2 ∂β ∂(μ.prod ρ) := integral_prod _ hsw
    _ = ∫ x, ∫ u, ∫ b, Φ b x u ∂β ∂ρ ∂μ :=
        integral_prod (fun y : X × U => ∫ b, Φ b y.1 y.2 ∂β) hsw.integral_prod_left
end GlobalTheory.QuotIntFJ
