-- Prove2me | solution 2 for GlobalTheory.CubeColim.trans_congr
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T22:51:17.72454+00:00
-- url     : https://prove2.me/submissions/31588034-ddda-4f18-8ed3-78bb2488bac6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechComplexDirectLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Filter
open GlobalTheory
open GlobalTheory.CubeColim
variable {ι : Type} [LinearOrder ι] [Fintype ι]

theorem solution {A : ℕ → Cube.{0} ι ℤ} (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d))
    {j j' c d : ℕ} (h : c + j = d) (h' : c + j' = d) (e : j = j') : μ j c d h = μ j' c d h' := by
  subst j'
  rfl
