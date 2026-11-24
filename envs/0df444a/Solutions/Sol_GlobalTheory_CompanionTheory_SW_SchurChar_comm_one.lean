-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.comm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:21.36118+00:00
-- url     : https://prove2.me/submissions/c521b623-16ad-40e7-b13a-c2c4361940f5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AdelicProofs_SchurTranslationsCharacters

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
theorem _root_.solution (T : (V → ℂ) → (V → ℂ)) : Comm T (fun _ => 1) :=
  ⟨IsLocallyConstant.const 1, fun φ _ => by simp⟩
end GlobalTheory.CompanionTheory.SW.SchurChar
