-- Prove2me | solution 1 for GlobalTheory.T.fourier_inversion_schwartz_bruhat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:24.883854+00:00
-- url     : https://prove2.me/submissions/3f145720-66d1-4ba2-9e59-4e113f1061b1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhat
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_sb
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FouSB_fou_sb


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FouSB.fou_sb | exact GlobalTheory.CompanionTheory.SW.FouSB.fou_sb | (intros; apply GlobalTheory.CompanionTheory.SW.FouSB.fou_sb <;> assumption)
end _root_.GlobalTheory.T
