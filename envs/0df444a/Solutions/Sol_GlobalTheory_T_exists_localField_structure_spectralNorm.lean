-- Prove2me | solution 1 for GlobalTheory.T.exists_localField_structure_spectralNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:50:05.855311+00:00
-- url     : https://prove2.me/submissions/be1f6397-8c63-4f19-852d-17f811e77f18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsNonarchimedeanLocalFieldSpectralNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsNonarchimedeanLocalFieldSpectralNormStatement
import Theorems.Thm_GlobalTheory_exists_isNonarchimedeanLocalField_spectralNorm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K], ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧ ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  first | exact @GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | exact GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | (intros; apply GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm <;> assumption)
end _root_.GlobalTheory.T
