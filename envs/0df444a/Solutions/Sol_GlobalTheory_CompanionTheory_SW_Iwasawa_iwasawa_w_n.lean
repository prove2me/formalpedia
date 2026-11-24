-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Iwasawa.iwasawa_w_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:55.969706+00:00
-- url     : https://prove2.me/submissions/a737d6c4-62fd-4034-ae1a-851369c8d0fc

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_idem_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_scale_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_Oh_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_Oh_neg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_Oh_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_scale_mul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_image_scale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_w_n_eq

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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ b : F,
    ∃ (y : A F) (a : (A F)ˣ) (k : SL(2, A F)), (∀ i j, k i j ∈ Oh F) ∧
      wMat * nMat (algebraMap F (A F) b) = nMat y * mMat a * k ∧
      (fun x => (a : A F) * x) '' Oh F = {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} := by
  intro F _ _ b
  refine ⟨(idem b - 1) * scale b, scaleUnit b, kMat b, ?_, ?_, image_scale b⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact Oh_sub (idem_mem b) Oh_one
    · exact idem_mem b
    · exact Oh_neg (scale_mem b)
    · exact Oh_neg (scale_mul_mem b)
  · exact w_n_eq _ (idem b) (scaleUnit b) (kMat b) rfl rfl rfl rfl (scale_combo b)
end GlobalTheory.CompanionTheory.SW.Iwasawa
