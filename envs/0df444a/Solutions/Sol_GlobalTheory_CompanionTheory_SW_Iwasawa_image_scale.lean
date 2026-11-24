-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.image_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:41:35.849806+00:00
-- url     : https://prove2.me/submissions/305f1689-e1ed-430c-bbb0-4f2694d3c72e

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_scale_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_Oh_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_scale_mul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Iwasawa
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.Iwasawa
theorem _root_.solution (b : F) :
    (fun x => scale b * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    refine ⟨Oh_mul (scale_mem b) ho, ?_⟩
    have : algebraMap F (A F) b * (scale b * o) = (scale b * algebraMap F (A F) b) * o := by ring
    show algebraMap F (A F) b * (scale b * o) ∈ Oh F
    rw [this]
    exact Oh_mul (scale_mul_mem b) ho
  · rintro ⟨hx, hbx⟩
    refine ⟨scaleInv b * x, fun v => ?_, ?_⟩
    · rw [mul_at]
      by_cases h : IntAt b v
      · rw [scaleInv_int h, one_mul]; exact hx v
      · rw [scaleInv_not h]; exact hbx v
    · show scale b * (scaleInv b * x) = x
      rw [← mul_assoc, scale_mul_scaleInv, one_mul]
end GlobalTheory.CompanionTheory.SW.Iwasawa
