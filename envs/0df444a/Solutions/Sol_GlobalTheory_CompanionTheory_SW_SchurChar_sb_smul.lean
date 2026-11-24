-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.sb_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:50.489984+00:00
-- url     : https://prove2.me/submissions/b8a25ec4-b049-4d14-a196-9c39f06db21c

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
theorem _root_.solution (c : ℂ) {φ : V → ℂ} (h : SB φ) : SB (c • φ) :=
  sb_mul (m := fun _ => c) (IsLocallyConstant.const c) h
end GlobalTheory.CompanionTheory.SW.SchurChar
