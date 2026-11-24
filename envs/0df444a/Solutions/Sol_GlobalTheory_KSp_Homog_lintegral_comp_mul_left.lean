-- Prove2me | solution 1 for GlobalTheory.KSp.Homog.lintegral_comp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:24:45.206401+00:00
-- url     : https://prove2.me/submissions/d4544646-7ca1-4075-b893-a59e89ae4dce

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMeasureEqSmulAddHaarLocalField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open ValuativeRel Topology
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.Homog
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable [MeasurableSpace F] [BorelSpace F]
namespace GlobalTheory.KSp.Homog
theorem _root_.solution (μ : Measure F)
    (hμ : ∀ x : F, x ≠ 0 → μ.map (fun y ↦ x * y) = (absE x)⁻¹ • μ) {f : F → ℝ≥0∞}
    (hf : Measurable f) {x : F} (hx : x ≠ 0) :
    ∫⁻ t, f (x * t) ∂μ = (absE x)⁻¹ * ∫⁻ t, f t ∂μ := by
  calc ∫⁻ t, f (x * t) ∂μ = ∫⁻ t, f t ∂(μ.map (fun y ↦ x * y)) :=
        (lintegral_map hf (measurable_const_mul x)).symm
    _ = _ := by rw [hμ x hx, lintegral_smul_measure]; rfl
end GlobalTheory.KSp.Homog
