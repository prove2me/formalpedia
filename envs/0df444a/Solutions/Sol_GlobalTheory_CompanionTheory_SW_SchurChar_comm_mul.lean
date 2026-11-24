-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.comm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:20.51349+00:00
-- url     : https://prove2.me/submissions/d811a968-21e8-49a9-87ec-b1cd8569c3ad

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_SchurChar_sb_mul

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
theorem _root_.solution {T : (V → ℂ) → (V → ℂ)} {m m' : V → ℂ} (h : Comm T m) (h' : Comm T m') :
    Comm T (fun u => m u * m' u) := by
  refine ⟨h.1.mul h'.1, fun φ hφ => ?_⟩
  have e : (fun u => m u * m' u * φ u) = fun u => m u * (m' u * φ u) := by
    funext u; exact mul_assoc _ _ _
  rw [e, h.2 _ (sb_mul h'.1 hφ), h'.2 φ hφ]
  funext u; exact (mul_assoc _ _ _).symm
end GlobalTheory.CompanionTheory.SW.SchurChar
