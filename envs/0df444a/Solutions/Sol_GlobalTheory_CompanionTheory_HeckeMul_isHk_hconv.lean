-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.isHk_hconv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:30:23.513799+00:00
-- url     : https://prove2.me/submissions/a75589db-15af-41d9-b50c-caead71292f0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_support_hconv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hconv_biinv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2 Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (hconv K e₁ e₂) := by
  refine ⟨h₁.1, h₁.2.1, ?_, fun k₁ hk₁ k₂ hk₂ g => hconv_biinv h₁ h₂ hk₁ hk₂ g⟩
  have hc : IsCompact (tsupport e₁ * tsupport e₂) := IsCompact.mul h₁.2.2.1 h₂.2.2.1
  exact HasCompactSupport.of_support_subset_isCompact hc (support_hconv K e₁ e₂)
end GlobalTheory.CompanionTheory.HeckeMul
