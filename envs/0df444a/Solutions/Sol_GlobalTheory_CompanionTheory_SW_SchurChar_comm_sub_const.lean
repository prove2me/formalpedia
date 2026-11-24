-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.comm_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:22.580098+00:00
-- url     : https://prove2.me/submissions/9ff9e086-35d0-4574-9ea8-d1a77af26556

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_smul

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SchurChar
variable {V : Type} [TopologicalSpace V]
namespace GlobalTheory.CompanionTheory.SW.SchurChar
theorem _root_.solution {T : (V → ℂ) → (V → ℂ)}
    (hadd : ∀ φ φ', SB φ → SB φ' → T (φ + φ') = T φ + T φ')
    (hsmul : ∀ (c : ℂ) φ, SB φ → T (c • φ) = c • T φ)
    {f : V → ℂ} (h : Comm T f) (c : ℂ) : Comm T (fun u => f u - c) := by
  refine ⟨h.1.sub (IsLocallyConstant.const c), fun φ hφ => ?_⟩
  have e : (fun u => (f u - c) * φ u) = (fun u => f u * φ u) + (-c) • φ := by
    funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, hadd _ _ (sb_mul h.1 hφ) (sb_smul _ hφ), hsmul _ _ hφ, h.2 φ hφ]
  funext u; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
end GlobalTheory.CompanionTheory.SW.SchurChar
