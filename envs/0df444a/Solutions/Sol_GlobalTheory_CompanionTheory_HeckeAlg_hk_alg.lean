-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeAlg.hk_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:50:25.119262+00:00
-- url     : https://prove2.me/submissions/980f990e-4313-421e-900a-65cfb7fa66fd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeAlgebraStructure
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeAdj_hk_adjoint
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFix_hk_mem_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_hconv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_hconv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAlg
namespace GlobalTheory.CompanionTheory.HeckeAlg
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], HkAlg F ι := by
  intro F _ _ _ _ ι _ _
  unfold HkAlg
  intro K e₁ e₂ h₁ h₂
  obtain ⟨hstar₁, hadj⟩ := GlobalTheory.CompanionTheory.HeckeAdj.hk_adjoint F ι K e₁ h₁
  refine ⟨GlobalTheory.CompanionTheory.HeckeMul.isHk_hconv h₁ h₂, hstar₁, ?_⟩
  intro V _ _ ρ v hv
  exact ⟨(GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e₁ h₁ V ρ v hv).1,
    GlobalTheory.CompanionTheory.HeckeMul.hk_hconv h₁ h₂ ρ hv,
    fun B hB w hw => hadj V ρ B hB v hv w hw⟩
end GlobalTheory.CompanionTheory.HeckeAlg
