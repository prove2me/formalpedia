-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.sb_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:32:23.403441+00:00
-- url     : https://prove2.me/submissions/0d2bbc2f-b7d9-4134-9905-d4cd1b8180d4

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
theorem _root_.solution {φ φ' : V → ℂ} (h : SB φ) (h' : SB φ') : SB (φ + φ') :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩
end GlobalTheory.CompanionTheory.SW.SchurChar
