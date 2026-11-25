-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeMul.hk_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:35:05.009882+00:00
-- url     : https://prove2.me/submissions/629852b9-bf11-4c72-9891-78bef841f149

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_hconv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_hconv

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
namespace GlobalTheory.CompanionTheory.HeckeMul
theorem _root_.solution : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ), IsHk K e₁ → IsHk K e₂ → IsHk K (hconv K e₁ e₂) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K, hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) := by
  intro F _ _ _ _ ι _ _ K e₁ e₂ h₁ h₂
  exact ⟨isHk_hconv h₁ h₂, fun V _ _ ρ v hv => hk_hconv h₁ h₂ ρ hv⟩
end GlobalTheory.CompanionTheory.HeckeMul
