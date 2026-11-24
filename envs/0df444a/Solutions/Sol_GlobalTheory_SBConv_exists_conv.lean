-- Prove2me | solution 1 for GlobalTheory.SBConv.exists_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:27.330841+00:00
-- url     : https://prove2.me/submissions/d0c585bb-d4f9-4146-8bd9-9701350c1ce8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Theorems.Thm_GlobalTheory_SBConv_isLocallyConstant_translate
import Theorems.Thm_GlobalTheory_exists_weakIntegral_of_isLocallyConstant_of_isCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
noncomputable section
open GlobalTheory GlobalTheory.SBConv
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
namespace GlobalTheory.SBConv
theorem _root_.solution [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (Φ Ψ : SB G) :
    ∃ w : SB G, (∀ x, w.1 x = ∫ y, Φ.1 y * Ψ.1 (x - y) ∂μ) ∧
      ∀ l : SB G →ₗ[ℂ] ℂ, l w = ∫ y, Φ.1 y * l (translate Ψ y) ∂μ := by
  have hT : IsLocallyConstant (fun y => Φ.1 y • translate Ψ y) :=
    IsLocallyConstant.comp₂ Φ.2.1 (isLocallyConstant_translate Ψ) (fun c f => c • f)
  have hz : ∀ y, y ∉ tsupport Φ.1 → Φ.1 y • translate Ψ y = 0 := by
    intro y hy
    have h0 : Φ.1 y = 0 := by
      by_contra h
      exact hy (subset_tsupport _ h)
    rw [h0, zero_smul]
  obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact G μ (SB G)
    (fun y => Φ.1 y • translate Ψ y) hT (tsupport Φ.1) Φ.2.2.isCompact hz
  refine ⟨w, fun x => ?_, fun l => ?_⟩
  · exact hw ((LinearMap.proj x).comp (SB G).subtype)
  · rw [hw l]
    simp only [map_smul, smul_eq_mul]
end GlobalTheory.SBConv
