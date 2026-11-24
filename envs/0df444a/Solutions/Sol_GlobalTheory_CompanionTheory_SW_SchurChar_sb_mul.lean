-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.SchurChar.sb_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:34.79959+00:00
-- url     : https://prove2.me/submissions/eec68a55-09b8-4f0a-bcb6-f4d1725d9ad6

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
theorem _root_.solution {m φ : V → ℂ} (hm : IsLocallyConstant m) (h : SB φ) :
    SB (fun u => m u * φ u) :=
  ⟨hm.mul h.1, h.2.mul_left⟩
end GlobalTheory.CompanionTheory.SW.SchurChar
